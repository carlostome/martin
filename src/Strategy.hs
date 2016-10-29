module Strategy where

import ProofSearch
import Data.List

-- | A strategy describing how to solve a clause towards an auto-generated model solution
data ClauseStrategy
  = SplitStrategy String [ClauseStrategy]
  -- ^ @Split v next@ splits on variable @v@ in the current holes, and applies the strategies
  -- in @next@ to the corresponding new clause. An empty list of subordinate clauses indicates
  -- that the split introduced an absurd-pattern.
  | RefineStrategy [Proof]
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
    ("refine with:\n    " ++ intercalate "," (map proofToStr pr))
  show FailStrategy = "fail"

