{-# LANGUAGE DeriveFunctor, FlexibleContexts #-}
module Main where

-- import qualified Agda.Syntax.Abstract as A
-- import qualified Agda.Syntax.Translation.ConcreteToAbstract as Agda
-- import qualified Agda.TheTypeChecker as Agda
-- import qualified Agda.TypeChecking.Monad.Base as TCMonad
-- import qualified Agda.TypeChecking.Monad.State as TCMonad
-- import qualified Agda.TypeChecking.Monad.Options as TCMonad
-- import qualified Agda.TypeChecking.Errors as Agda
-- import qualified Agda.Syntax.Concrete as Agda
-- import qualified Agda.Syntax.Common as Agda
-- import qualified Agda.Main as Agda
-- import qualified Agda.Syntax.Parser as Agda
-- import qualified Agda.Syntax.Literal as Agda
-- import qualified Agda.Syntax.Fixity as Agda
-- import qualified Agda.Utils.FileName as Agda
-- import qualified Agda.Interaction.Imports as Interaction
-- import qualified Agda.Interaction.Options as Interaction
-- import Agda.Syntax.Abstract.Pretty

import           Lib
import           Strategy
import           ProofSearch

import Control.Arrow (first, second)
import           Control.Exception
import           Control.Monad.IO.Class
import Control.Monad.State
import Control.Monad.RWS
import Control.Monad.Writer
import           Data.Foldable
import qualified Data.HashMap.Strict      as HMS
import qualified Data.List                as List
import           Data.Monoid
import qualified Options.Applicative      as OA
import           System.IO
import           Text.Printf

data MartinOpt = MartinOpt
  { agdaFile :: FilePath
  }

progOptionParser :: OA.Parser MartinOpt
progOptionParser = MartinOpt
  <$> OA.argument OA.str
        (OA.metavar "FILE"
         <> OA.help "Path of the Agda file containing the exercise")

main :: IO ()
main = undefined

{- OUTDATED
main :: IO ()
main = OA.execParser opts >>= runMartin
  where
    opts = OA.info (OA.helper <*> progOptionParser)
      ( OA.fullDesc
      <> OA.progDesc "Run the tutor on the Agda exercise in FILE"
      <> OA.header "martin - an interactive Agda tutor"
      )

runMartin :: MartinOpt -> IO ()
runMartin opts = do
  printf "Starting tutor with %s\n" (agdaFile opts)
  -- absPath <- Agda.absolute $ agdaFile opts
  --  moduleSrc <- Agda.parseFile' Agda.moduleParser (Agda.mkAbsolute $ agdaFile opts)
  -- REMARK: the code below seems to be the "standard way" of performing type checking in an interactive setting
  {- Agda.runTCMPrettyErrors $ do
    TCMonad.resetState
    TCMonad.setCommandLineOptions Interaction.defaultOptions
    (iface, warnings) <- Interaction.typeCheckMain absPath
    case warnings of
      Interaction.NoWarnings -> return ()
      Interaction.SomeWarnings w -> return ()-- Agda.warningsToError w
    liftIO $ forM_ (HMS.toList $ TCMonad._sigDefinitions (TCMonad.iSignature iface)) $ \(k,v) ->
      printf "%s : %s\n\n" (show k) (show $ TCMonad.defType v)
  -}
  -- TODO: parsing
  printf "Type checking...\n"
  -- TODO: type checking
  
  -- TODO: pass additional state to interactive loop, wrap in TCM monad if necessary
  -- Imagine here that we have loaded the map example
  let u = Var (Raw "undefined")
      mapStrategy =
        [ SplitStrategy "xs"
          [ RefineStrategy (Proof "nil" [] u)
          , RefineStrategy (Proof "cons" [Proof "f" [Proof "x" [] u] u, Proof "map" [Proof "f" [] u, Proof "xs" [] u] u] u)
          ]
        ]
      partialSolution = [EmptyClause]
  printStudentState partialSolution
  let (p1, m1) = split [0] "xs" 2 partialSolution mapStrategy
  printStudentState p1
  print m1
  let (p2, m2) = refine [0,1] "map" 2 p1 mapStrategy
  printStudentState p2
  print m2
  return ()

-- | A partial refinement for a clause
data PartialRefinement
  = Hole
  -- ^ the refinement still contains a hole
  | RefinedWith String [PartialRefinement]
  -- ^ a refinement using an identifier and a given number of argument
  deriving (Show, Read, Eq, Ord)

-- | Partial solution for a clause.
data PartialClause
  = RefinedClause PartialRefinement
  -- ^ a clause has been refined
  | SplitClause String [PartialClause]
  -- ^ the clause has been split on a variable, resulting in a number of new clauses
  | EmptyClause
  -- ^ the clause is still empty (a hole at top level)
  deriving (Show, Read, Eq, Ord)

-- | A partial solution for an exercise consists of partial solutions for each clause.
type PartialSolution = [PartialClause]

-- | Path leading to a hole, described by the index of the branch taken at each level.
-- This is used by the user to reference holes.
type Path = [Int]

printStudentState :: MonadIO m => PartialSolution -> m ()
printStudentState = printClauses [] where
  printClauses path clauses = zipWithM_ printClause ((\i -> path ++ [i]) <$> [0..]) clauses
  printClause path (RefinedClause ref) = printRefinement path ref >> line
  printClause path (SplitClause _ cs) = printClauses path cs
  printClause path EmptyClause = printHole path >> line

  printHole path = liftIO $ printf "{%s}" $ show path

  printRefinement path Hole = printHole path
  printRefinement path (RefinedWith ref cs) = do
    liftIO $ printf "(%s" ref
    zipWithM_ (\p r -> space >> printRefinement p r)
      ((\i -> path ++ [i]) <$> [0..])
      cs
    liftIO $ printf ")"

  space = liftIO $ printf " "
  line = liftIO $ printf "\n"

targetList :: Applicative m => (a -> b -> m a) -> Int -> [a] -> [b] -> m [a]
targetList f = go where
  go 0 [] [] = error "invalid path"
  go 0 (x:xs) (y:_) = (:xs) <$> f x y
  go n (x:xs) (_:ys) = (x:) <$> go (n - 1) xs ys
  go _ _ _ = modelMismatch

-- | Performs a refinement by the student on the current exercise state and returns
-- the updated state and a value indicating whether the refinement adhered to the model solution.
-- If nothing is returned, the student still follows the model solution, otherwise, the part
-- of the model solution that differs is returned.
refine :: Path -- ^ the hole to refine
       -> String -- ^ identifier to fill in the hole
       -> Int -- ^ arity (number of arguments) of the identifier used for refinement, look up in environment before calling
       -> PartialSolution -- ^ current state of what student did
       -> ExerciseStrategy -- ^ strategy for current state of student
       -> (PartialSolution, Maybe (Either ClauseStrategy Proof))
refine holePath userRef arity st strat = second getAlt $ runWriter (goClauses holePath st strat) where
  goClauses (branch:path) cs args = targetList (goClause path) branch cs args
  goClauses [] [] [] = return []
  goClauses _ _ _ = error "invalid path"

  goClause path (SplitClause a excs) (SplitStrategy b stcs)
    | a == b = SplitClause a <$> goClauses path excs stcs
  goClause path (RefinedClause ref) (RefineStrategy prf)
    = RefinedClause <$> goRef path ref prf
  goClause path EmptyClause clauseStrat
    | null path = do
        case clauseStrat of
          RefineStrategy prf -> unless (proofRule prf == userRef) $ tell $ Alt $ Just $ Right prf
          SplitStrategy{} -> tell $ Alt $ Just (Left clauseStrat)
        return $ RefinedClause $ RefinedWith userRef (List.replicate arity Hole)
    | otherwise = error "invalid path"
  goClause _ _ _ = modelMismatch

  -- ASSUMPTION: arity parameter matches length of rule's args, because arity should have been looked up from the Agda file
  goRef path Hole prf
    | null path = do
        unless (proofRule prf == userRef) $ tell $ Alt $ Just $ Right prf
        return $ RefinedWith userRef (List.replicate arity Hole)
    | otherwise = error "invalid path"
  goRef (branch:path) (RefinedWith ref cs) (Proof rule args _)
    | ref == rule = RefinedWith ref <$> targetList (goRef path) branch cs args
  goRef _ _ _ = modelMismatch

-- | Performs a case-split by the student on the current exercise state and returns
-- the updated state and a value indicating whether the refinement adhered to the model solution.
-- If nothing is returned, the student still follows the model solution, otherwise, the part
-- of the model solution that differs is returned.
split :: Path
      -> String
      -> Int
      -> PartialSolution
      -> ExerciseStrategy
      -> (PartialSolution, Maybe (Either ClauseStrategy Proof))
split holePath userVar arity partSol exStrat = second getAlt $ runWriter (goClauses holePath partSol exStrat) where
  goClauses (branch:path) cs args = targetList (goClause path) branch cs args
  goClauses [] [] [] = return []
  goClauses _ _ _ = error "invalid path"

  goClause path (SplitClause a excs) (SplitStrategy b stcs)
    | a == b = SplitClause a <$> goClauses path excs stcs
  goClause path EmptyClause strat
    | null path = do
        case strat of
          SplitStrategy modelVar _
            | modelVar == userVar -> return ()
            | otherwise -> tell $ Alt $ Just (Left strat)
          -- model solution wants to refine here
          RefineStrategy _ -> tell $ Alt $ Just (Left strat)
        return $ SplitClause userVar (List.replicate arity EmptyClause)
    | otherwise = error "invalid path"
  goClause _ (RefinedClause _) (RefineStrategy _)
    = error "cannot split in refined clauses"
  goClause _ _ _ = modelMismatch

modelMismatch :: a
modelMismatch = error "model does not match already constructed part of user solution, something went wrong on the way"

-}
