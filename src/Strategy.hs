module Strategy where

import ProofSearch

-- | A strategy describing how to solve a clause towards an auto-generated model solution
data ClauseStrategy
  = SplitStrategy String [ClauseStrategy]
  -- ^ @Split v next@ splits on variable @v@ in the current holes, and applies the strategies
  -- in @next@ to the corresponding new clause. An empty list of subordinate clauses indicates
  -- that the split introduced an absurd-pattern.
  | RefineStrategy Proof
  -- ^ refines the current hole with a proof found by the proof search
  deriving (Show, Read, Eq, Ord)

-- | A strategy for solving an exercise consists of one strategy for each clause of the exercise
type ExerciseStrategy = [ClauseStrategy]
