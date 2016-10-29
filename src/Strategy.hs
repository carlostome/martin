{-# LANGUAGE TypeSynonymInstances, FlexibleInstances, FlexibleContexts #-}
module Strategy where

import ProofSearch
import Data.List
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
import           Agda.Syntax.Position
import           Agda.Syntax.Scope.Base
import qualified           Agda.Syntax.Internal.Names as I
import           Agda.Syntax.Translation.ConcreteToAbstract
import           Agda.TheTypeChecker
import           Agda.TypeChecking.Monad
import           Agda.TypeChecking.Errors
import           Agda.Utils.FileName
import           Agda.Utils.FileName
import           Agda.Utils.Hash
import           Agda.Utils.IO.Binary
import           Agda.Utils.Lens
import           Agda.Utils.Monad hiding (ifM)
import           Agda.Utils.Null
import           Agda.Utils.Pretty
import           Agda.Utils.Time
import qualified Agda.Utils.Trie                            as Trie
import Control.Monad.Trans.Maybe
import Control.Monad
import Control.Applicative
import qualified MakeCaseModified as MC
import           Control.DeepSeq
import           Control.Monad.Except
import           Control.Monad.IO.Class
import           Control.Monad.State.Strict
import Control.Monad.Extra
import Control.Monad.Writer
import Control.Monad.Reader
import qualified Data.List                                  as List
import qualified Data.Set                                  as Set
import           System.FilePath                            ((</>))
import Text.Printf
import Debug.Trace
import Data.Generics.Geniplate
import SearchTree
import Data.List ((\\))
import Data.Monoid
import Data.Maybe (catMaybes, listToMaybe)

import           ProofSearch
import           Translation

-- | A strategy describing how to solve a clause towards an auto-generated model solution
data ClauseStrategy
  = SplitStrategy String [ClauseStrategy]
  -- ^ @Split v next@ splits on variable @v@ in the current holes, and applies the strategies
  -- in @next@ to the corresponding new clause. An empty list of subordinate clauses indicates
  -- that the split introduced an absurd-pattern.
  | RefineStrategy Proof
  -- ^ refines the current hole with a proof found by the proof search
  | FailStrategy
  deriving (Read, Eq, Ord)

-- | A strategy for solving an exercise consists of one strategy for each clause of the exercise
type ExerciseStrategy = [ClauseStrategy]

instance Show ClauseStrategy where
  show (SplitStrategy s cl) = unlines
    (("split at " ++ s ++ " and:") :
     map (("  "++) . show) cl)
  show (RefineStrategy pr) =
    ("refine with: " ++ proofToStr pr)
  show FailStrategy = "fail"

debug :: (MonadIO m, Show a) => a -> m ()
debug str = when True (liftIO (print str))

-- | Apply a proof search strategy,
-- if not possible select a variable and split.
proofSearchStrategy :: TCEnv
                    -> TCState
                    -> [A.Declaration]
                    -> (I.MetaInfo, InteractionId)
                    -> IO ClauseStrategy
proofSearchStrategy tce tcs prog hole@(mi,ii) = do
  debug ("proofSearchStrategy " ++ show ii)
  -- First we check whether the meta is in a top level rhs.
  ((goal, hdb),_) <- runTCM tce tcs $ goalAndRules ii
  let prfs = iddfs $ cutoff 5 $ solve goal hdb
  solution <- runMaybeT . msum . map (trySolution tce tcs prog hole) $ prfs
  case solution of
    Just proof -> return (RefineStrategy proof)
    Nothing
      | checkTopLevel (mi,ii) prog ->
         splitVarStrategy tce tcs prog hole
      | otherwise -> return FailStrategy

-- | Select a variable in the scope of an Interation id
-- to split.
selectVarToSplit :: [A.Declaration]
                 -> (I.MetaInfo, InteractionId)
                 -> String
selectVarToSplit prog hole@(mi,ii)=
  let (x:xs) = map snd $ scopeLocals $ metaScope mi
  in show (localVar x)


-- | Try a Proof to see if it typechecks termination checker.
-- A known problem with this function is if the we feed the hole
-- with a non structurally smaller expression then it just loops.
-- This bug also happens in Agda #2286
trySolution :: TCEnv -> TCState -> [A.Declaration]
            -> (I.MetaInfo, InteractionId)
            -> Proof -> MaybeT IO Proof
trySolution tce tcmState prog hole@(mi,ii) proof = mapMaybeT (fmap fst . runTCM tce tcmState) $ do
  debug ("trying solution: " ++ proofToStr proof)
  -- Save the old TCM state because proofToAbstractExpr may change it.
  expr <- lift $ B.parseExprIn ii noRange (proofToStr proof)
  -- Replace the hole in the old program with the new expression.
  let newProg = replaceHole ii expr prog
  -- Try to typecheck the new program.
  put tcmState
  tryIt (lift $ checkDecls newProg)
        (const (return proof))
        (const mzero)


-- | Replaces a hole identified by its interaction id with a new expression.
replaceHole :: A.ExprLike e => InteractionId -> A.Expr -> e -> e
replaceHole ii repl = A.mapExpr $ \e -> case e of
                                  A.QuestionMark _ iiq
                                    | iiq == ii -> repl
                                  other -> other

-- | Split a given variable in an InteractionId
splitVarStrategy :: TCEnv -> TCState
                         -> [A.Declaration]
                         -> (I.MetaInfo, InteractionId)
                         -> IO ClauseStrategy
splitVarStrategy tce tcs prog hole@(mi,ii) = do
  let var = selectVarToSplit prog hole
  debug ("splitting on var: " ++ var)
  ((_, newClauses),tcs') <- runTCM tce tcs (MC.makeCase ii noRange var)
  let newProg  = replaceClauses ii newClauses prog
  ((newP, oldMetas),tcs'') <- runTCM tce tcs' $ do
     (newDecl,oldMetas) <- rebuildInteractionPoints newProg
     checkDecls newDecl
     unfreezeMetas
     return (newDecl,oldMetas)
  let newMetas = [(mi, ii) | A.QuestionMark mi ii <- concatMap universeBi newP
                          , not (ii `elem` oldMetas) ]
  SplitStrategy var <$> mapM (proofSearchStrategy tce tcs'' newP) newMetas


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
generateStrategy :: TCState -> [A.Declaration] -> IO [ClauseStrategy]
generateStrategy tcs prog = do
  (newDecls, tcs') <- runTCM initEnv tcs $ do
    (newDecl,_) <- rebuildInteractionPoints prog
    checkDecls newDecl
    unfreezeMetas
    return newDecl
  let metas = [(mi, ii) | A.QuestionMark mi ii <- concatMap universeBi newDecls]
  debug ("Generate strategy for metas: "
         ++ intercalate "," (map (show . snd) metas))
  mapM (proofSearchStrategy initEnv tcs' newDecls) metas

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
  { buildStrategy :: [A.Declaration] -> IO [ClauseStrategy] }

initSession :: Int -> IO Session
initSession verbosity = do
  debug "Initializing session"
  (tcmState,_) <- runTCM initEnv initState $ initAgda verbosity
  return $ Session
     { buildStrategy = \decls -> generateStrategy tcmState decls }

-- | Try a computation, executing either the success handler with the result
-- or the error handler with the caught exception.
tryIt :: MonadError e m => m a -> (a -> m b) -> (e -> m b) -> m b
tryIt act success failure = do
  r <- fmap Right act `catchError` \e -> return $ Left e
  either failure success r

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


