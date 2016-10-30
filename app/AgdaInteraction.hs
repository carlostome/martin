{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeSynonymInstances  #-}
{-# LANGUAGE UndecidableInstances  #-}
module AgdaInteraction where

import qualified Agda.Interaction.BasicOps                  as B
import qualified Agda.Syntax.Abstract                       as A
import           Agda.Syntax.Abstract.Pretty
import           Agda.Syntax.Common
import           Agda.Syntax.Translation.ConcreteToAbstract
import           Agda.TheTypeChecker
import           Agda.TypeChecking.Errors
import           Agda.TypeChecking.Monad
import           Agda.Utils.FileName
import           Agda.Utils.Pretty

import qualified MakeCaseModified                           as MC

import           Control.DeepSeq
import           Control.Lens
import           Control.Monad.Except
import           Control.Monad.IO.Class
import           Control.Monad.Reader
import           Control.Monad.State.Strict
import           Control.Monad.Writer
import qualified Data.List                                  as List
import qualified Data.Set                                   as Set
import           Debug.Trace
import           System.Console.Haskeline
import qualified System.Console.Haskeline                   as HaskEx
import           System.FilePath                            ((</>))
import qualified Text.ParserCombinators.ReadP               as ReadP
import qualified Text.ParserCombinators.ReadPrec            as ReadPrec
import           Text.Printf
import           Text.Read                                  (readPrec)

import           Data.Generics.Geniplate
import           Data.List                                  ((\\))
import           Data.Maybe                                 (catMaybes,
                                                             listToMaybe)
import           Data.Monoid
import           SearchTree

import qualified AgdaUtil                                   as AU
import qualified Strategy                                   as S

-- | An exercise is just an Agda file, represented by the declarations inside it.
-- INVARIANT: this state needs to be kept in sync with the TCM state.
-- To prevent headaches, only modify the list of declarations (aka the user program)
-- when the changes have been type checked and the TCM state has been populated with
-- the declarations.
data ExerciseState = ExerciseState
  { _exerciseProgram  :: S.StatefulProgram
  -- ^ the current state of the program
  , _exerciseStrategy :: Maybe S.ExerciseStrategy
  , _exerciseUndo     :: [(S.StatefulProgram, Maybe S.ExerciseStrategy)]
  -- ^ a history of program states
  }

makeLenses ''ExerciseState

-- | Environment for exercise computation.
data ExerciseEnv = ExerciseEnv
  { _exerciseFile    :: AbsolutePath
  , _exerciseTCState :: TCState
  , _exerciseTCEnv   :: TCEnv
  }

makeLenses ''ExerciseEnv

newtype PrettyTCErr = PrettyTCErr { getPrettyTCErr :: String }
  deriving (Show)

instance Exception PrettyTCErr

-- | I'm sorry for another Monad stack, but somewhere we need to keep track of
-- information related to the exercise session.
type ExerciseM = InputT (ReaderT ExerciseEnv (StateT ExerciseState IO))

-- * Interfacing with User

-- | Runs an interactive user session, loading the given exercise
-- This should be the main entry point for everything having to do with Agda.
runInteractiveSession :: Int -> FilePath -> IO ()
runInteractiveSession verbosity agdaFile = do
  -- load the Agda file
  (absPath, module') <- AU.parseAgdaFile agdaFile
  (ret, progState) <- runTCM initEnv initState
    $ local (\e -> e { envCurrentPath = Just absPath })
    $ flip catchError (prettyError >=> return . Left ) $ Right <$> do
    -- load Level primitives and setup TCM state
    initialState <- AU.initAgda verbosity -- the number is the verbosity level, useful for debugging
    -- REMARK: initialState should now contain a snapshot of an initialized Agda session and can be used to quickly
    -- revert when we need to recheck the exercise code.
    -- convert exercise to abstract syntax
    abstractDecls <- toAbstract module'
    -- check that the exercise is valid to begin with
    checkDecls abstractDecls
    unfreezeMetas

    return (initialState, abstractDecls)
  case ret of
    Left err -> printf "Exercise session failed with\n%s\n" err
    Right (initialState, decls) -> do
      session <- S.initSession verbosity absPath
      str <- S.buildStrategy session decls

      let exEnv = ExerciseEnv
            { _exerciseFile = absPath
            , _exerciseTCState = initialState
            , _exerciseTCEnv = initEnv { envCurrentPath = Just absPath }
            }
          exState = ExerciseState
            { _exerciseProgram = S.StatefulProgram decls progState
            , _exerciseStrategy = str
            , _exerciseUndo = []
            }

      putStrLn $ unlines
        [ "Welcome to Martin - the interactive Agda tutor"
        , "You have loaded exercise " ++ show absPath
        , "Type `h` to get help!"
        , ""
        ]

      let go = do
            prettyProgram >>= outputStrLn
            outputStrLn ""
            exerciseLoop
      void $ runStateT (runReaderT (runInputT defaultSettings go) exEnv) exState

data TopCommand
  = CmdTopUndo
  | CmdTopSelect Int
  | CmdTopExit
  | CmdTopHelp
  | CmdTopPrint
  deriving (Eq, Ord, Show, Read)

data HoleCommand
  = CmdHoleType
  | CmdHoleContext
  | CmdRefine String
  | CmdSplit String
  | CmdHoleLeave
  deriving (Eq, Ord, Show, Read)

readPTopCommand :: ReadP.ReadP TopCommand
readPTopCommand = msum
  [ CmdTopUndo <$ ReadP.char 'u'
  , CmdTopExit <$ ReadP.char 'q'
  , CmdTopHelp <$ ReadP.char 'h'
  , CmdTopPrint <$ ReadP.char 'p'
  , CmdTopSelect <$> (ReadP.char 's' *> ReadP.skipSpaces *> ReadPrec.readPrec_to_P readPrec 0)
  ]

readPHoleCommand :: ReadP.ReadP HoleCommand
readPHoleCommand = msum
  [ CmdHoleType <$ ReadP.char 't'
  , CmdHoleContext <$ ReadP.char 'c'
  , CmdHoleLeave <$ ReadP.char 'l'
  , CmdRefine <$> (ReadP.char 'r' *> ReadP.skipSpaces *> ReadP.many1 ReadP.get)
  , CmdSplit <$> (ReadP.char 's' *> ReadP.skipSpaces *> ReadP.many1 ReadP.get)
  ]

runReadP :: ReadP.ReadP a -> String -> Maybe a
runReadP p s =
  case [ x | (x,"") <- ReadPrec.readPrec_to_S (ReadPrec.lift p) 0 s ] of
    [x] -> Just x
    _   -> Nothing

exerciseLoop :: ExerciseM ()
exerciseLoop = do
  minput <- getInputLine "% "
  let cmd = maybe (Just CmdTopExit) (runReadP readPTopCommand) minput
  catchTCMErr exerciseLoop $ case cmd of
    Nothing -> do
      outputStrLn "Unknown command!"
      exerciseLoop
    Just CmdTopUndo -> do
      undo >>= \case
        True -> outputStrLn "Undone!"
        False -> outputStrLn "Cannot undo!"
      exerciseLoop
    Just CmdTopExit -> outputStrLn "Bye!"
    Just (CmdTopSelect hole) -> do
      tcs <- use $ exerciseProgram . S.programTCState
      let ii = InteractionId hole
      (ips, _) <- runTCMEx tcs getInteractionPoints
      if ii `elem` ips then do
        outputStrLn $ "Focusing on hole " ++ show ii
        handle (\Interrupt -> return ()) $ withInterrupt $ holeLoop ii
      else
        outputStrLn "A hole with this number does not exist!"
      exerciseLoop
    Just CmdTopHelp -> do
      outputStrLn $ unlines
        [ "Available commands at the top level:"
        , "  h          print this help"
        , "  u          undo last step"
        , "  s <hole>   select hole with number <hole>"
        , "  p          print the program"
        , "  q          quit program"
        , ""
        , "Available commands in a hole"
        , "  l          leave the hole"
        , "  t          print the type of the hole"
        , "  c          print the context of the hole"
        , "  r <def>    refine the hole with definition <def>"
        , "  s <var>    split variable <var>"
        ]
      exerciseLoop
    Just CmdTopPrint -> do
      prettyProgram >>= outputStrLn
      exerciseLoop

catchTCMErr :: MonadException m => InputT m a -> InputT m a -> InputT m a
catchTCMErr cont act = HaskEx.catch act $ \e -> do
  outputStrLn "Agda returned an error:\n"
  outputStrLn $ getPrettyTCErr e
  cont

holeLoop :: InteractionId -> ExerciseM ()
holeLoop ii = do
  minput <- getInputLine $ show ii ++ "% "
  let cmd = maybe (Just CmdHoleLeave) (runReadP readPHoleCommand) minput
  catchTCMErr (holeLoop ii) $ case cmd of
    Nothing -> do
      outputStrLn "Unknown command!"
      holeLoop ii
    Just CmdHoleLeave -> return ()
    Just CmdHoleType -> do
      tcs <- use $ exerciseProgram . S.programTCState
      (doc, _) <- runTCMEx tcs $ B.typeOfMeta B.Normalised ii >>= \(B.OfType _ ty) -> prettyA ty
      outputStrLn $ render doc
      holeLoop ii
    Just CmdHoleContext -> do
      tcs <- use $ exerciseProgram . S.programTCState
      let prettyCtx (name, ty) = do
            let pname = pretty $ either id A.qnameName name
            pty <- prettyA ty
            return $ pname <+> char ':' <+> pty
      (doc, _) <- runTCMEx tcs $ AU.thingsInScopeWithType ii >>= mapM prettyCtx
      outputStrLn $ render $ vcat doc
      holeLoop ii
    Just (CmdSplit var) -> do
      -- TODO: split
      holeLoop ii
    Just (CmdRefine def) -> do
      -- TODO: refine
      holeLoop ii

undo :: ExerciseM Bool
undo = use exerciseUndo >>= \case
  [] -> return False
  (prog,strat):rest -> do
    exerciseUndo .= rest
    exerciseProgram .= prog
    exerciseStrategy .= strat
    return True

-- | Adds the current program and TCM state to the undo history.
recordState :: ExerciseM ()
recordState = do
  step <- (,) <$> use exerciseProgram <*> use exerciseStrategy
  exerciseUndo %= cons step

-- | Displays the current state of the program to the user.
-- It also shows the numbers (InteractionId) of each hole. Based on that, the user can then
-- choose to perform an action on a given hole.
prettyProgram :: ExerciseM String
prettyProgram = do
  prog <- use exerciseProgram
  fmap fst $ runTCMEx (view S.programTCState prog) $ do
    let decls = AU.setMetaNumbersToInteraction (view S.programDecls prog)
    render . vcat <$> mapM prettyA decls

runTCMEx :: TCState -> TCM a -> ExerciseM (a, TCState)
runTCMEx tcs tcm = do
  env <- view exerciseTCEnv
  liftIO $ runTCM env tcs $ tcm `catchError` (prettyError >=> HaskEx.throwIO . PrettyTCErr)

    -- -- run user session
    -- st <- execStateT (runReaderT exerciseSession exEnv) exState
    -- -- if all went well, st contains the solved exercise
    -- -- TODO: pretty print and send to teacher ;)
    -- return ()
  -- -- print errors
{-

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
  isTopLevelHole (A.ScopedExpr _ e)       = isTopLevelHole e
  isTopLevelHole _                        = Nothing

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

-- | Takes a proof and converts it to an abstract expression in the context of the given hole.
proofToAbstractExpr :: InteractionId -> Proof -> TCM A.Expr
proofToAbstractExpr ii proof = B.parseExprIn ii noRange (proofStr proof) where
  proofStr (Proof name args _)
    | List.null args = name
    | otherwise = "(" ++ List.unwords (name : map proofStr args) ++ ")"

-- | Replaces a hole identified by its interaction id with a new expression.
replaceHole :: A.ExprLike e => InteractionId -> A.Expr -> e -> e
replaceHole ii repl = A.mapExpr $ \e -> case e of
                                  A.QuestionMark _ iiq
                                    | iiq == ii -> repl
                                  other -> other
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

-}


instance MonadState s m => MonadState s (InputT m) where
  get = lift get
  put = lift . put

instance MonadReader e m => MonadReader e (InputT m) where
  ask = lift ask
  local f = mapInputT (local f)
