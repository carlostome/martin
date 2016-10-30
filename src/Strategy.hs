{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeSynonymInstances  #-}
module Strategy where

import qualified Agda.Interaction.BasicOps       as B
import           Agda.Interaction.FindFile
import           Agda.Interaction.Imports
import           Agda.Interaction.Options
import qualified Agda.Interaction.Options.Lenses as Lens
import qualified Agda.Syntax.Abstract            as A
import qualified Agda.Syntax.Abstract.Views      as A
import qualified Agda.Syntax.Internal            as I
import           Agda.Syntax.Common
import           Agda.Syntax.Info                as I
import           Agda.Syntax.Position
import           Agda.Syntax.Scope.Base
import           Agda.TheTypeChecker
import           Agda.TypeChecking.Monad
import           Agda.Utils.FileName
import           Agda.Utils.Monad                hiding (ifM)
import qualified Agda.Utils.Trie                 as Trie

import           Control.Arrow                   ((&&&))
import qualified Control.Exception               as E
import           Control.Lens
import           Control.Monad
import           Control.Monad.Except
import           Control.Monad.Reader
import           Control.Monad.State.Strict
import           Control.Monad.Trans.Maybe
import           Control.Monad.Writer
import           Control.Concurrent
import           Data.Generics.Geniplate
import qualified Data.List                       as List
import           Debug.Trace
import           System.FilePath                 ((</>))

import qualified MakeCaseModified                as MC
import qualified ProofSearch                     as P
import           SearchTree
import           Translation

-- | A strategy describing how to solve a clause towards an auto-generated model solution
data ClauseStrategy
  = SplitStrategy String [ClauseStrategy]
  -- ^ @Split v next@ splits on variable @v@ in the current holes, and applies the strategies
  -- in @next@ to the corresponding new clause. An empty list of subordinate clauses indicates
  -- that the split introduced an absurd-pattern.
  | RefineStrategy P.Proof
  -- ^ refines the current hole with a proof found by the proof search
  -- | FailStrategy
  deriving (Read, Eq, Ord)

-- | A strategy for solving an exercise consists of one strategy for each clause of the exercise
type ExerciseStrategy = [ClauseStrategy]

instance Show ClauseStrategy where
  show (SplitStrategy s cl) = unlines
    (("split at " ++ s ++ " and:") :
     map (("  "++) . show) cl)
  show (RefineStrategy pr) =
    "refine with: " ++ P.proofToStr pr

-- | Pairs an abstract Agda program with the type checker state after checking said program.
data StatefulProgram = StatefulProgram
  { _programDecls   :: [A.Declaration]
  , _programTCState :: TCState
  -- ^ the state of the type checker after checking the program.
  -- In particular, all interaction points are registered and paired with the corresponding meta variables.
  }
makeLenses ''StatefulProgram

data SearchEnvironment = SearchEnvironment
  { _initialTCState :: TCState
  -- ^ the initial state just after loading the Agda primitives.
  -- No user bindings have been checked yet.
  , _initialTCEnv   :: TCEnv
  -- Constructor depth of a variable for it to be eligible for splitting on
  , _depthLimit     :: Int
  }
makeLenses ''SearchEnvironment

type Search = MaybeT (ReaderT SearchEnvironment IO)

debug :: (MonadIO m, Show a) => a -> m ()
debug str = when False (liftIO (print str))

-- | Apply a proof search strategy,
-- if not possible select a variable and split.
proofSearchStrategy :: StatefulProgram
                    -> InteractionId
                    -> Search ClauseStrategy
proofSearchStrategy prog ii = do
  debug ("proofSearchStrategy " ++ show ii)
  -- First we check whether the meta is in a top level rhs.
  ((goal, hdb),_) <- runTCMSearch (view programTCState prog) $ goalAndRules ii
  debug goal
  let prfs = iddfs $ cutoff 7 $ P.solve goal hdb
  mplus (RefineStrategy <$> msum (map (trySolution prog ii) prfs))
        (do guard (checkTopLevel ii (view programDecls prog))
            splitStrategy prog ii)

-- | Select a variable in the scope of an Interation id
-- to split.
selectVarsToSplit :: StatefulProgram
                 -> InteractionId
                 -> Search [String]
selectVarsToSplit prog ii = do
  se <- lift ask
  (vars, _) <- runTCMSearch (view programTCState prog) (f (_depthLimit se))
  return vars
    where 
      f lim = do
        m <- lookupInteractionId ii
        -- Find the clause that contains this goal
        (_,_,cl) <- MC.findClause m
            -- From the clause we get all patterns
        let dBrPats = deBruijnPats cl
            -- List of all found variables with their constructor depth
            allVarDepths = concat $ map varLevels dBrPats
            -- Only tuples whose constructor depth was at most the given limit
            varDepthsLim = filter (\(n, _) -> n <= lim) allVarDepths
            -- sorted by constructor depth from lowest to highest
            sortedVarDepths = List.sort varDepthsLim
        -- We no longer need the constructor depths at this point
        return $ map snd sortedVarDepths


deBruijnPats :: I.Clause -> [I.DeBruijnPattern]
deBruijnPats cl = map namedArg $ I.namedClausePats cl

-- 1. Removes the order indice in the DeBruijnPattern.
-- 2. Finds all variables in the pattern and assigns it a hierarchy level of 0
-- 3. For every cons that we pass through we increment the hierarchy level
-- 4. Returns a list of tuple of a variable and its hierarchy level
varLevels :: I.DeBruijnPattern -> [(Int, String)]
varLevels dBrPat = varLevel' (fmap snd dBrPat)
  where
    varLevel' (I.VarP x)
      | x /= "_"              = [(0, x)]
      | otherwise             = []
    varLevel' (I.ConP _ _ xs) = map (\(n,x) -> (n + 1, x)) $ concat $ map (varLevel' . namedArg) xs
    varLevel' _               = []


-- | Try a Proof to see if it typechecks termination checker.
-- A known problem with this function is if the we feed the hole
-- with a non structurally smaller expression then it just loops.
-- This bug also happens in Agda #2286
trySolution :: StatefulProgram
            -> InteractionId
            -> P.Proof -> Search P.Proof
trySolution prog ii proof = do
  debug ("trying solution: " ++ P.proofToStr proof)
  -- Save the old TCM state because proofToAbstractExpr may change it.
  (expr, tcs') <- runTCMSearch (view programTCState prog) $ B.parseExprIn ii noRange (P.proofToStr proof)
  -- Replace the hole in the old program with the new expression.
  let newProg = views programDecls (replaceHole ii expr) prog
  -- Try to typecheck the new program.
  fmap fst . runTCMSearchFresh $ do
    (ds, _) <- rebuildInteractionPoints newProg
    debug "checking filled hole inside TCM"
    checkDecls ds
    debug "checked filled hole inside TCM"
    unfreezeMetas
    return proof

-- | Replaces a hole identified by its interaction id with a new expression.
replaceHole :: A.ExprLike e => InteractionId -> A.Expr -> e -> e
replaceHole ii repl = A.mapExpr $ \e -> case e of
                                  A.QuestionMark _ iiq
                                    | iiq == ii -> repl
                                  other -> other

-- | Try splitting on variables given in an InteractionId
splitStrategy :: StatefulProgram
              -> InteractionId
              -> Search ClauseStrategy
splitStrategy prog ii = do
  vars <- selectVarsToSplit prog ii
  msum $ map (splitSingleVarStrategy prog ii) vars

-- | Split a given variable in an InteractionId
splitSingleVarStrategy :: StatefulProgram -> InteractionId -> String -> Search ClauseStrategy
splitSingleVarStrategy prog ii var = do
  debug ("splitting on var: " ++ var)
  ((_, newClauses),_) <- runTCMSearch (view programTCState prog) $ MC.makeCase ii noRange var
  debug ("new clauses: " ++ show newClauses)
  ((newDecls, oldMetas),tcs) <- runTCMSearchFresh $ do
     (interactionDecls, oldMetas) <- rebuildInteractionPoints (views programDecls (replaceClauses ii newClauses) prog)
     checkDecls interactionDecls
     unfreezeMetas
     return (interactionDecls,oldMetas)
  let newProg = StatefulProgram
        { _programDecls = newDecls
        , _programTCState = tcs
        }
  let newMetas = [ newii | A.QuestionMark _ newii <- concatMap universeBi newDecls
                         , newii `notElem` oldMetas ]
  SplitStrategy var <$> mapM (proofSearchStrategy newProg) newMetas

runTCMSearch :: TCState -> TCM a -> Search (a, TCState)
runTCMSearch tcs tcm = do
  tce <- view initialTCEnv
  r <- liftIO $ (Right <$> runTCM tce tcs tcm) `E.catch` (\(e :: TCErr) -> return $ Left e)
  case r of
    Left e -> traceShowM e >> mzero
    Right v  -> return v

runTCMSearchFresh :: TCM a -> Search (a, TCState)
runTCMSearchFresh tcm = view initialTCState >>= flip runTCMSearch tcm

-- | Replaces all question marks with fresh interaction points and registers them with the type checker.
-- This step is necessary after resetting the type checker state.
rebuildInteractionPoints :: A.ExprLike e
                          => e -> TCM (e,[InteractionId])
rebuildInteractionPoints e = runWriterT (A.traverseExpr go e) where
  go (A.QuestionMark m ii) = do
    nii <- lift $ registerInteractionPoint noRange Nothing
    when (ii /= (-1)) $ tell [nii]
    return (A.QuestionMark m nii)
  go other = return other

-- | Check if the Hole is in a top level position.
checkTopLevel :: InteractionId -> [A.Declaration] -> Bool
checkTopLevel ii = any look
  where
    look (A.Mutual _ decls)             = any look decls
    look (A.Section _ _ _ decls)        = any look decls
    look (A.RecDef _ _ _ _ _ _ _ decls) = any look decls
    look (A.ScopedDecl _ decls)         = any look decls
    look (A.FunDef _ _ _ clauses)       = any lookClause clauses
    look _                              = False

    lookClause cls = case A.clauseRHS cls of
      A.RHS e -> isTopLevelHole e
      _       -> False

    isTopLevelHole (A.QuestionMark _ hole) = ii == hole
    isTopLevelHole (A.ScopedExpr _ e)      = isTopLevelHole e
    isTopLevelHole _                       = False

-- | Generate a Strategy given a list of Declaration.
-- This is the top level function.
generateStrategy :: [A.Declaration] -> Search [ClauseStrategy]
generateStrategy prog = do
  (newDecls, tcs') <- runTCMSearchFresh $ do
    (newDecl,_) <- rebuildInteractionPoints prog
    checkDecls newDecl
    unfreezeMetas
    return newDecl
  let metas = [ ii | A.QuestionMark mi ii <- concatMap universeBi newDecls]
      sprog = StatefulProgram newDecls tcs'
  debug ("Generate strategy for metas: " ++ show metas)
  mapM (proofSearchStrategy sprog) metas

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

data Session = Session
  { buildStrategy :: [A.Declaration] -> IO (Maybe [ClauseStrategy]) }

initSession :: Int -> AbsolutePath -> IO Session
initSession verbosity path = do
  debug "Initializing session"
  (tcmState,_) <- runTCM initEnv initState $ initAgda verbosity
  let env = SearchEnvironment
        { _initialTCState = tcmState
        , _initialTCEnv   = initEnv { envCurrentPath = Just path }
        , _depthLimit     = 6
        }
  return Session
     { buildStrategy = \decls -> runReaderT (runMaybeT (generateStrategy decls)) env }

-- | Try a computation, executing either the success handler with the result
-- or the error handler with the caught exception.
tryIt :: MonadError e m => m a -> (a -> m b) -> (e -> m b) -> m b
tryIt act success failure = do
  r <- fmap Right act `catchError` \e -> return $ Left e
  either failure success r

tryItIO :: IO a -> (a -> IO b) -> (E.SomeException -> IO b) -> IO b
tryItIO act success failure = do
  r <- fmap Right act `E.catch` \e -> return $ Left e
  either failure success r

-- | Replaces the clause identified by the interaction id of its single RHS hole
-- with the list of new clauses.
replaceClauses :: InteractionId -> [A.Clause] -> [A.Declaration] -> [A.Declaration]
replaceClauses ii newClauses = map update where
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
    let locals = map (A.nameConcrete &&& LocalVar) $ clauseLocals $ A.clauseLHS clause
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


