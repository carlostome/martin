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
import           Agda.Syntax.Common
import           Agda.Syntax.Info                as I
import qualified Agda.Syntax.Internal            as I
import           Agda.Syntax.Position
import           Agda.Syntax.Scope.Base
import           Agda.TheTypeChecker
import           Agda.TypeChecking.Monad
import           Agda.Utils.FileName
import           Agda.Utils.Monad                hiding (ifM)
import qualified Agda.Utils.Trie                 as Trie

import           Control.Arrow                   ((&&&))
import           Control.Concurrent
import qualified Control.Exception               as E
import           Control.Lens
import           Control.Monad
import           Control.Monad.Except
import           Control.Monad.Reader
import           Control.Monad.State.Strict
import           Control.Monad.Trans.Maybe
import           Control.Monad.Writer
import           Data.Generics.Geniplate
import qualified Data.List                       as List
import qualified Data.Either                     as ETH
import           Debug.Trace
import           System.FilePath                 ((</>))

import qualified AgdaUtil                        as AU
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
        (do guard (AU.checkTopLevel ii (view programDecls prog))
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
            allVarDepths = concatMap varDepths dBrPats
            -- Only tuples whose constructor depth was at most the given limit
            varDepthsLim = filter (\(n, _) -> n <= lim) allVarDepths
            -- sorted by constructor depth from lowest to highest
            sortedVarDepths = List.sort varDepthsLim
        -- Find all local variables in scope
        localVars <- AU.varsInScope ii
        -- Only visible local variables can be split on
        return $ List.intersect (map snd sortedVarDepths) (map show localVars)


deBruijnPats :: I.Clause -> [I.DeBruijnPattern]
deBruijnPats cl = map namedArg $ I.namedClausePats cl

-- 1. Removes the order indice in the DeBruijnPattern.
-- 2. Finds all variables in the pattern and assigns it a constructor depth of 0
-- 3. For every cons that we pass through we increment the constructor depth
-- 4. Returns a list of tuple of a variable and its constructor depth
varDepths :: I.DeBruijnPattern -> [(Int, String)]
varDepths dBrPat = varLevel' (fmap snd dBrPat)
  where
    varLevel' (I.VarP x)
    -- We can't split on an underscore
      | x /= "_"              = [(0, x)]
      | otherwise             = []
    varLevel' (I.ConP _ _ xs) = map (\(n,x) -> (n + 1, x)) $ concatMap (varLevel' . namedArg) xs
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
  let newProg = views programDecls (AU.replaceHole ii expr) prog
  -- Try to typecheck the new program.
  fmap fst . runTCMSearchFresh $ do
    (ds, _) <- AU.rebuildInteractionPoints newProg
    debug "checking filled hole inside TCM"
    checkDecls ds
    debug "checked filled hole inside TCM"
    unfreezeMetas
    return proof

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
     (interactionDecls, oldMetas) <- AU.rebuildInteractionPoints (views programDecls (AU.replaceClauses ii newClauses) prog)
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
    Left _  -> mzero
    Right v -> return v

runTCMSearchFresh :: TCM a -> Search (a, TCState)
runTCMSearchFresh tcm = view initialTCState >>= flip runTCMSearch tcm

-- | Generate a Strategy given a list of Declaration.
-- This is the top level function.
generateStrategy :: [A.Declaration] -> Search [ClauseStrategy]
generateStrategy prog = do
  (newDecls, tcs') <- runTCMSearchFresh $ do
    (newDecl,_) <- AU.rebuildInteractionPoints prog
    checkDecls newDecl
    unfreezeMetas
    return newDecl
  let metas = [ ii | A.QuestionMark mi ii <- concatMap universeBi newDecls]
      sprog = StatefulProgram newDecls tcs'
  debug ("Generate strategy for metas: " ++ show metas)
  mapM (proofSearchStrategy sprog) metas

data Session = Session
  { buildStrategy :: [A.Declaration] -> IO (Maybe [ClauseStrategy]) }

initSession :: Int -> AbsolutePath -> IO Session
initSession verbosity path = do
  debug "Initializing session"
  (tcmState,_) <- runTCM initEnv initState $ AU.initAgda verbosity
  let env = SearchEnvironment
        { _initialTCState = tcmState
        , _initialTCEnv   = initEnv { envCurrentPath = Just path }
        , _depthLimit     = 6
        }
  return Session
     { buildStrategy = \decls -> runReaderT (runMaybeT (generateStrategy decls)) env }


