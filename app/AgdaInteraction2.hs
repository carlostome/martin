{-# LANGUAGE TypeSynonymInstances, FlexibleInstances, FlexibleContexts #-}
module AgdaInteraction2 where

import qualified Agda.Interaction.BasicOps                  as B
import           Agda.Interaction.FindFile
import           Agda.Interaction.Imports
import           Agda.Interaction.InteractionTop
import           Agda.Interaction.MakeCase
import           Agda.Interaction.Options
import qualified Agda.Interaction.Options.Lenses            as Lens
import           Agda.Main
import qualified Agda.Syntax.Abstract                       as A
import qualified Agda.Syntax.Abstract.Views                 as A
import           Agda.Syntax.Abstract.Pretty
import           Agda.Syntax.Common
import           Agda.Syntax.Info as I
import           Agda.Syntax.Concrete
import           Agda.Syntax.Concrete.Generic as C
import           Agda.Syntax.Fixity
import           Agda.Syntax.Literal
import           Agda.Syntax.Parser
import           Agda.Syntax.Position
import           Agda.Syntax.Scope.Base
import qualified           Agda.Syntax.Internal.Names as I
import           Agda.Syntax.Translation.AbstractToConcrete
import           Agda.Syntax.Translation.ConcreteToAbstract
import           Agda.TheTypeChecker
import           Agda.TypeChecking.Monad
import           Agda.TypeChecking.Errors
import           Agda.Utils.FileName
import           Agda.Utils.FileName
import           Agda.Utils.Hash
import           Agda.Utils.IO.Binary
import           Agda.Utils.Lens
import           Agda.Utils.Monad
import           Agda.Utils.Null
import           Agda.Utils.Pretty
import           Agda.Utils.Time
import qualified Agda.Utils.Trie                            as Trie

import           ProofSearch
import           Translation

import qualified MakeCaseModified as MC

import           Control.DeepSeq
import           Control.Monad.Except
import           Control.Monad.IO.Class
import           Control.Monad.State.Strict
import Control.Monad.Writer
import Control.Monad.Reader
import qualified Data.List                                  as List
import qualified Data.Set                                  as Set
import           System.FilePath                            ((</>))
import Text.Printf

import Debug.Trace

import Data.Generics.Geniplate
import Strategy
import SearchTree
import Data.List ((\\))
import Data.Monoid
import Data.Maybe (catMaybes, listToMaybe)

-- | An exercise is just an Agda file, represented by the declarations inside it.
-- INVARIANT: this state needs to be kept in sync with the TCM state.
-- To prevent headaches, only modify the list of declarations (aka the user program)
-- when the changes have been type checked and the TCM state has been populated with
-- the declarations.
data ExerciseState = ExerciseState
  { exerciseDecls :: [A.Declaration]
  -- ^ the current state of the program
  , exerciseUndo :: [([A.Declaration], TCState)]
  -- ^ a history of program states
  }

-- | Environment for exercise computation.
data ExerciseEnv = ExerciseEnv
  { exerciseFile :: AbsolutePath
  , exerciseVerbosity :: Int
  , exerciseInitialAgdaState :: TCState
  }

-- | I'm sorry for another Monad stack, but somewhere we need to keep track of
-- information related to the exercise session.
type ExerciseM = ReaderT ExerciseEnv (StateT ExerciseState TCM)

-- * Interfacing with User

-- | Runs an interactive user session, loading the given exercise
-- This should be the main entry point for everything having to do with Agda.
runInteractiveSession :: Int -> FilePath -> IO ()
runInteractiveSession verbosity agdaFile = do
  -- load the Agda file
  absPath            <- absolute agdaFile
  (_, module'@([Module _ _ _ concreteDecls])) <- parseFile' moduleParser absPath
  -- TODO: inject pragmas // Carlos: We shouldn't care about pragmas
  ret <- runTCMPrettyNoExit $ local (\e -> e { envCurrentPath = Just absPath }) $ do
    -- load Level primitives and setup TCM state
    initialState <- initAgda verbosity -- the number is the verbosity level, useful for debugging
    -- REMARK: initialState should now contain a snapshot of an initialized Agda session and can be used to quickly
    -- revert when we need to recheck the exercise code.

    -- convert exercise to abstract syntax
    abstractDecls <- toAbstract module'

    -- check that the exercise is valid to begin with
    checkDecls abstractDecls


    unfreezeMetas -- IMPORTANT: if metas are not unfrozen, we cannot refine etc.

    str <- generateStrategy initialState abstractDecls
    liftIO (print str)

    -- setup initial state and the environment
    let exState = ExerciseState
          { exerciseDecls = abstractDecls
          , exerciseUndo = [] }
        exEnv = ExerciseEnv
          { exerciseFile = absPath
          , exerciseVerbosity = verbosity
          , exerciseInitialAgdaState = initialState
          }
    -- run user session
    st <- execStateT (runReaderT exerciseSession exEnv) exState
    -- if all went well, st contains the solved exercise
    -- TODO: pretty print and send to teacher ;)
    return ()
  -- print errors
  case ret of
    Left err -> printf "Exercise session failed with\n%s\n" err
    Right _ -> return ()


-- | Apply a proof search strategy,
-- if not possible select a variable and split.
proofSearchStrategy :: TCState
                    -> [A.Declaration]
                    -> (I.MetaInfo, InteractionId)
                    -> TCM ClauseStrategy
proofSearchStrategy tcs prog hole@(mi,ii) = do
  -- First we check whether the meta is in a top level rhs.
  (goal, hdb) <- goalAndRules prog ii
  let prfs = dfs $ cutoff 10 $ solve goal hdb
  if checkTopLevel (mi,ii) prog
     then do
       liftIO (print $ "Top level: " ++ show ii)
       let var = selectVarToSplit prog hole
       liftIO (print $ "Selected variable: " ++ var )
       if List.null prfs
          then splitWithVarAtIdStrategy tcs var prog hole
          else do
            solution <- trySolutions tcs prog hole prfs
            maybe (splitWithVarAtIdStrategy tcs var prog hole)
                  (return . RefineStrategy)
                  solution
     else do
       if List.null prfs
          then return FailStrategy
          else do
            solution <- trySolutions tcs prog hole prfs
            maybe (return FailStrategy)
                  (return . RefineStrategy)
                  solution

-- | Select a variable in the scope of an Interation id
-- to split.
selectVarToSplit :: [A.Declaration]
                 -> (I.MetaInfo, InteractionId)
                 -> String
selectVarToSplit prog hole@(mi,ii)=
  let (x:xs) = map snd $ scopeLocals $ metaScope mi
  in show (localVar x)


type Success a = Either a ()
failS   = Right ()
succedS = Left

give
  :: InteractionId  -- ^ Hole.
  -> A.Expr         -- ^ The expression to give.
  -> TCM Bool       -- ^ If successful, the very expression is returned unchanged.
give ii e = liftTCM $ do
  -- if Range is given, update the range of the interaction meta
  mi  <- lookupInteractionId ii
  -- Try to give mi := e
  tryIt (B.giveExpr mi e)
        (const (return True))
        (const (return False))

-- | Try a Proof to see if it typechecks/passes termination checker.
trySolutions :: TCState -> [A.Declaration]
            -> (I.MetaInfo, InteractionId)
            -> [Proof] -> TCM (Maybe Proof)
trySolutions tcs prog hole@(mi,ii) []  = return Nothing
trySolutions tcs prog hole@(mi,ii) (proof:prs)  =
  do aexpr <- proofToAbstractExpr ii proof
     liftIO (print (proofToStr proof))
     success <- give ii aexpr
     if success
       then do
         let newProg = replaceHole ii aexpr prog
         put tcs
         tryIt (checkDecls newProg)
               (\_ -> do unfreezeMetas
                         liftIO (print "BP 6")
                         return (Just proof))
               (const (trySolutions tcs prog hole prs))
       else
        trySolutions tcs prog hole prs


-- | Split a given variable in an InteractionId
splitWithVarAtIdStrategy :: TCState -> String
                         -> [A.Declaration]
                         -> (I.MetaInfo, InteractionId)
                         -> TCM ClauseStrategy
splitWithVarAtIdStrategy tcs var prog (mi,ii) = do
  (_, newClauses) <- MC.makeCase ii noRange var
  let newProg  = replaceClauses ii newClauses prog
  put tcs
  (newP, oldMetas) <- rebuildInteractionPoints' newProg
  checkDecls newP
  unfreezeMetas
  let newMetas = [(mi, ii) | A.QuestionMark mi ii <- concatMap universeBi newP
                          , not (ii `elem` oldMetas) ]
  liftIO (print "hola")
  SplitStrategy var <$> mapM (proofSearchStrategy tcs newProg) newMetas


-- | Replaces all question marks with fresh interaction points and registers them with the type checker.
-- This step is necessary after resetting the type checker state.
rebuildInteractionPoints' :: A.ExprLike e
                          => e -> TCM (e,[InteractionId])
rebuildInteractionPoints' e = runWriterT (A.traverseExpr go e) where
  go (A.QuestionMark m ii) = do
    nii <- lift $ registerInteractionPoint noRange Nothing
    when (ii /= (-1)) $ tell [nii]
    return (A.QuestionMark m nii)
  go other = return other

-- | Check if the Hole is in a top level position.
checkTopLevel :: (I.MetaInfo, InteractionId) -> [A.Declaration] -> Bool
checkTopLevel (mi, ii) = or . map look
  where
    look (A.Mutual _ decls)      = or $ map look decls
    look (A.Section _ _ _ decls) = or $ map look decls
    look (A.RecDef _ _ _ _ _ _ _ decls) = or $ map look decls
    look (A.ScopedDecl _ decls)         = or $ map look decls
    look (A.FunDef _ _ _ clauses) = or $ map lookClause clauses
    look _ = False

    lookClause cls = case A.clauseRHS cls of
      A.RHS e -> isTopLevelHole e
      _ -> False

    isTopLevelHole (A.QuestionMark mi hole) = ii == hole
    isTopLevelHole (A.ScopedExpr _ e)       = isTopLevelHole e
    isTopLevelHole _ = False

-- | Generate a Strategy given a list of Declaration.
-- This is the top level function.
generateStrategy :: TCState -> [A.Declaration] -> TCM [ClauseStrategy]
generateStrategy tcs prog = do
  let metas = [(mi, ii) | A.QuestionMark mi ii <- concatMap universeBi prog]
  liftIO (print . map snd $ metas)
  mapM (proofSearchStrategy tcs prog) metas

-- | This is where all the exercise solving should happen
exerciseSession :: ExerciseM ()
exerciseSession = do
  -- REMARK: How a session should be structured:
  -- 1. given the current state of the program, invoke proof search to generate strategy (See module Strategy)
  --    (if it is not possible to solve, tell the user so, in order for him to backtrack)
  -- 2. let the user do stuff
  --    * if the user follows the strategy, just refine or split and return to 2
  --    * if the user diverts from the strategy, go to 1, or undo step
  -- 3. no holes left -> user happy

  -- THIS IS JUST AN INTERACTIVE LOOP ALLOWING TO EITHER REFINE OR SPLIT HOLES, TO SEE WHETHER IT'S ACTUALLY WORKING
  forever $ do
    showProgramToUser
    liftIO $ putStrLn "InteractionID:"
    ii <- InteractionId <$> liftIO readLn `catchError` \_ -> return (-1)
    when (ii >= 0) $ do
      liftIO $ putStrLn "Action:"
      act <- liftIO $ getLine
      let wrapAction act = do
            recordState -- save state for undoing
            tryIt act
              (\_ -> do -- success
                  liftIO $ printf "recorded step\n"
                  tcmToEx $ getInteractionIdsAndMetas >>= mapM_
                    (\(ii, mi) -> do
                        meta <- getMetaInfo <$> lookupMeta mi
                        liftIO $ printf "Scope for %s:\n" (show ii)
                        liftIO $ print (clScope meta)
                        liftIO $ printf "\n\n")
              )
              (\e -> do -- failure
                  str <- tcmToEx $ prettyError e
                  liftIO $ printf "step did not type check: %s\n" str
                  void $ undo
              )
      case act of
        ('r':' ':ref) -> wrapAction $ performUserAction ii (UserRefine ref)
        ('c':' ':var) -> wrapAction $ performUserAction ii (UserSplit var)
        "u" -> undo >>= liftIO . print
        "s" -> tcmToEx $ thingsInScopeWithType  ii >>= liftIO . print
        _ -> liftIO $ putStrLn "try again"

-- | Replaces the clause identified by the interaction id of its single RHS hole
-- with the list of new clauses.
replaceClauses :: InteractionId -> [A.Clause] -> [A.Declaration] -> [A.Declaration]
replaceClauses ii newClauses prog = map update prog where
  -- recursively traverses all declarations to replace the clauses
  update (A.Mutual mi decls) = A.Mutual mi (map update decls)
  update (A.Section mi mn bnds decls) = A.Section mi mn bnds (map update decls)
  update (A.FunDef di qn del clauses) = A.FunDef di qn del $ concatMap updateClause clauses
  update (A.RecDef di qn1 ri flag qn2 bnds e decls) = A.RecDef di qn1 ri flag qn2 bnds e (map update decls)
  update (A.ScopedDecl si decls) = A.ScopedDecl si (map update decls)
  update other = other

  updateClause cls = case A.clauseRHS cls of
    A.RHS e -> case isTopLevelHole e of
      -- the newly generated meta variables inherit the scope information of the
      -- variable they are replacing. Since we are operating on abstract syntax,
      -- which is the stage after scope checking, we need to track scope manually here.
      -- initScope updates the local variables of the old meta variable's scope
      Just (mi, hole) | hole == ii -> map (initScope $ metaScope mi) newClauses
      _ -> [cls]
    A.WithRHS qn exprs clauses ->
      let newrhs = A.WithRHS qn exprs (concatMap updateClause clauses)
      in [cls { A.clauseRHS = newrhs}]
    _ -> [cls]

  -- checks whether there is a top level hole in the expression of a clause
  isTopLevelHole (A.QuestionMark mi hole) = Just (mi, hole)
  isTopLevelHole (A.ScopedExpr _ e) = isTopLevelHole e
  isTopLevelHole _ = Nothing

  initScope scope clause =
    -- here we need to extract all the bound names in the patterns of the clause and insert
    -- them into the top level scope
    let locals = map (\n -> (A.nameConcrete n, LocalVar n)) $ clauseLocals $ A.clauseLHS clause
        newScope = scope { scopeLocals = locals }
        -- update scoped things in the expression with the new scope
        updScope (A.ScopedExpr _ e) = A.ScopedExpr newScope e
        updScope (A.QuestionMark mi hole) = A.QuestionMark mi { metaScope = newScope } hole
        updScope o = o
    in A.mapExpr updScope clause

  -- finds all local variables in a clause
  -- REMARK: currently only works for patterns, not co-patterns
  clauseLocals (A.LHS _ (A.LHSHead _ pats) _) = concatMap (patternDecls . namedThing . unArg) pats
  clauseLocals _ = []

  -- finds all variables bound in patterns, only constructors and variables supported so far
  -- not sure what else we need, but we'll find out sooner or later
  patternDecls (A.VarP n) = [n]
  patternDecls (A.ConP _ _ a) = concatMap (patternDecls . namedThing . unArg) a
  patternDecls (A.DefP _ _ a) = concatMap (patternDecls . namedThing . unArg) a
  patternDecls _ = []

-- | Replaces a hole identified by its interaction id with a new expression.
replaceHole :: A.ExprLike e => InteractionId -> A.Expr -> e -> e
replaceHole ii repl = A.mapExpr $ \e -> case e of
                                  A.QuestionMark _ iiq
                                    | iiq == ii -> repl
                                  other -> other

-- | Adds the current program and TCM state to the undo history.
recordState :: ExerciseM ()
recordState = do
  prog <- gets exerciseDecls
  tc <- saveTCState
  modify $ \s -> s { exerciseUndo = (prog, tc) : exerciseUndo s }

data UserAction
  = UserRefine String
  | UserSplit String

-- | Type checks a new state of the program and update, if successful.
-- May fail with an exception if any step goes wrong. Restoring state
-- should be handled by caller.
performUserAction :: InteractionId -> UserAction -> ExerciseM ()
performUserAction hole action = do
  -- apply action to generate new program
  newprog <- case action of
    UserRefine estr -> do
      -- parse the user input in the given context
      given <- tcmToEx $ B.parseExprIn hole noRange estr
      -- try to refine the hole with the user expression
      expr <- tcmToEx $ B.give hole Nothing given
      -- replace hole in AST
      replaceHole hole expr <$> gets exerciseDecls
    UserSplit var -> do
      -- invoke case splitting functionality
      (ctx, newClauses) <- tcmToEx $ MC.makeCase hole noRange var
      -- ctx seems only to be relevant when splitting in extended lambdas, not something we do
      replaceClauses hole newClauses <$> gets exerciseDecls
  -- type check
  resetTCState
  -- rebuild interaction points (normally only created when going from concrete -> abstract)
  newprog' <- rebuildInteractionPoints newprog
  -- check updated AST (might not succeed if the termination checker intervenes)
  tcmToEx $ do
    checkDecls newprog'
    unfreezeMetas
  modify $ \s -> s { exerciseDecls = newprog' }

undo :: ExerciseM Bool
undo = do
  hist <- gets exerciseUndo
  case hist of
    (prog,st):rest -> do
      restoreTCState st
      tcmToEx $ getInteractionIdsAndMetas >>= liftIO . print
      modify $ \s -> s { exerciseUndo = rest, exerciseDecls = prog }
      return True
    _ -> return False

-- | Replaces all question marks with fresh interaction points and registers them with the type checker.
-- This step is necessary after resetting the type checker state.
rebuildInteractionPoints :: A.ExprLike e => e -> ExerciseM e
rebuildInteractionPoints = tcmToEx . A.traverseExpr go where
  go (A.QuestionMark m _) = A.QuestionMark m <$> registerInteractionPoint noRange Nothing
  go other = return other

-- | Reverts to a fresh Agda TCM state, forgetting all user definitions and retaining only the primitives
resetTCState :: ExerciseM ()
resetTCState = asks exerciseInitialAgdaState >>= restoreTCState

-- | Lift a TCM computation in the exercise monad.
-- Can't use 'MonadTCM' because that requires reader and state over
-- the TCM env and state and not our state.
tcmToEx :: TCM a -> ExerciseM a
tcmToEx = lift . lift

-- | Try a computation, executing either the success handler with the result
-- or the error handler with the caught exception.
tryIt :: MonadError e m => m a -> (a -> m b) -> (e -> m b) -> m b
tryIt act success failure = do
  r <- fmap Right act `catchError` \e -> return $ Left e
  either failure success r

-- | Returns the current TCM state.
saveTCState :: ExerciseM TCState
saveTCState = tcmToEx get

-- | Restores the TCM state.
restoreTCState :: TCState -> ExerciseM ()
restoreTCState = tcmToEx . put

-- | Displays the current state of the program to the user.
-- It also shows the numbers (InteractionId) of each hole. Based on that, the user can then
-- choose to perform an action on a given hole.
showProgramToUser :: ExerciseM ()
showProgramToUser = do
    prog <- setMetaNumbersToInteraction <$> gets exerciseDecls
    doc <- tcmToEx $ vcat <$> mapM prettyA prog  -- printDecls prog
    liftIO $ putStrLn $ render doc

refineWithProof :: InteractionId -> Proof -> ExerciseM ()
refineWithProof hole proof = return ()

-- * Interfacing with Agda

-- | In the abstract syntax, sets the 'metaNumber' of 'QuestionMark' to
-- the corresponding interaction ID to have it printed. Seems to be the suggested
-- way according to the documentation for 'QuestionMark'.
-- WARNING: This messes with the internal state of expressions which causes type checking to brake,
-- so only use before pretty printing.
setMetaNumbersToInteraction :: A.ExprLike e => e -> e
setMetaNumbersToInteraction = A.mapExpr go where
  go (A.QuestionMark meta ii) = A.QuestionMark meta { metaNumber = Just $ MetaId $ interactionId ii } ii
  go other = other

-- | Like 'runTCMPrettyErrors', but does not exit the application afterwards
runTCMPrettyNoExit :: TCM a -> IO (Either String a)
runTCMPrettyNoExit tcm = do
  ret <- runTCMTop $ (Right <$> tcm) `catchError` \err -> do
    str <- prettyError err
    return $ Left str
  case ret of
    Left _ -> return $ Left "impossible: this error should have been caught before"
    Right x -> return x

-- | This initializes the TCM state just enough to get everything started.
-- For now, it uses the default options and loads Agda's Level primitives.
initAgda :: Int -> TCM TCState
initAgda verbosity = do
  -- initialize interactive state
  resetAllState
  setCommandLineOptions defaultOptions
    { optPragmaOptions = (optPragmaOptions defaultOptions)
      { optVerbose = Trie.singleton [] verbosity }
    }

  -- ==================== BEGIN CODE FROM AGDA SOURCE
  libdir <- liftIO defaultLibDir
  -- To allow posulating the built-ins, check the primitive module
  -- in unsafe mode
  _ <- bracket_ (gets Lens.getSafeMode) Lens.putSafeMode $ do
    Lens.putSafeMode False
    -- Turn off import-chasing messages.
    -- We have to modify the persistent verbosity setting, since
    -- getInterface resets the current verbosity settings to the persistent ones.
    bracket_ (gets Lens.getPersistentVerbosity) Lens.putPersistentVerbosity $ do
      Lens.modifyPersistentVerbosity (Trie.delete [])  -- set root verbosity to 0
      -- We don't want to generate highlighting information for Agda.Primitive.
      withHighlightingLevel None $ do
        primitiveModule <- moduleName $ mkAbsolute $
            libdir </> "prim" </> "Agda" </> "Primitive.agda"
        getInterface_ primitiveModule
  -- ==================== END CODE FROM AGDA SOURCE
  -- return with state right after initialization, to be able to speed up things when we need to reset
  get


-- | Takes a proof and converts it to an abstract expression in the context of the given hole.
proofToAbstractExpr :: InteractionId -> Proof -> TCM A.Expr
proofToAbstractExpr ii proof = B.parseExprIn ii noRange (proofStr proof) where
  proofStr (Proof name args _)
    | List.null args = name
    | otherwise = "(" ++ List.unwords (name : map proofStr args) ++ ")"

-- | Returns everything that is in scope at a given interaction point.
-- The first A.Expr is either a Var referring to a local bound variable
-- or a Def referring to a global definition.
-- The second A.Expr is the type of that thing.
thingsInScopeWithType :: InteractionId -> TCM [(A.Expr, A.Expr)]
thingsInScopeWithType ii = do
  m <- lookupInteractionId ii
  mi <- lookupMeta m
  let s = getMetaScope mi
      locals = map (localVar . snd) $ scopeLocals s
      globals = Set.toList $ scopeInScope s
      allExprs = map A.Var locals ++ map A.Def globals
  types <- mapM (B.typeInMeta ii B.Normalised) allExprs
  let stuffWithTypes = zip allExprs types
  return stuffWithTypes

-- * Some functions solely used for testing stuff

itest2 :: FilePath -> IO ()
itest2 agdaFile = do
  -- load agda file
  path <- absolute agdaFile
  (pragmas, concreteDecls) <- parseFile' moduleParser path
  -- run TCM computation (inside Agda's type checking monad)
  runTCMPrettyErrors $ do
    -- load primitives like Level etc.
    initialState <- initAgda 0
    -- convert to abstract syntax
    abstractDecls <- toAbstract concreteDecls
    checkDecls abstractDecls
    -- print all interaction metas (i.e. holes in the program)
    getInteractionIdsAndMetas >>= liftIO . print

    -- TEST CODE for map function
    [(inil,mnil), (icons,mcons)] <- getInteractionIdsAndMetas
    forM_ itWorks $ \prf -> do
      liftIO $ print prf
      given <- proofToAbstractExpr icons prf
      pp <- prettyA given
      liftIO $ print $ render pp
    -- END TEST CODE

    -- try restoring the state
    put initialState
    getInteractionIdsAndMetas >>= liftIO . print -- prints [], so restoring actually works

    return ()

