{-# LANGUAGE FlexibleContexts #-}
module Main where

import           ProofSearch
import           SearchTree

import           Control.Monad.RWS
import qualified Options.Applicative as OA

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


-- | The available rules in the following context
--
-- @
--   map : (A -> B) -> Vec A n -> Vec B n
--   map f nil = nil
--   map f (cons x xs) = ?
-- @
--
-- The name of a rule is the name of the definition in Agda, i.e. we have rules named "map", "cons", "nil" etc.
-- For function types, the return type is the conclusion of the rule (i.e. this is what we unify against when we
-- want to construct a value of a given type) and the function arguments become the premises (the new holes that
-- need to be filled).
--
-- Note that type variables are only translated to actual proof search variables if they are introduced by a Pi-type
-- on the way. For example, we have variables in the rules for "map", "cons" and "nil", but not for "f", "x" or "xs",
-- because the variables have already been introduced into the scope. (We can't just unify the "A" and "B" in the
-- type of "f" with anything, because they appear as concrete types inside the function definition.)
--
-- Furthermore, sometimes we need to fill a hole of function type, as it is the case with the "f" argument of map.
-- Therefore, for every function we can also add a rule with the whole type of the function as a conclusion and no
-- premises. That will allow using unapplied functions itself as arguments.
--
-- Note that when pattern matching on the vector argument, we need to introduce some constants representing the length
-- of the tail, called @n'@ in the example below.
-- This should be just a matter of unifying the type of the constructor with the (instantiated) type of the argument.
--
-- TODO: find out how quantified variables are dealt with (I suppose they must be introduced as some fresh constants)
-- TODO: enforce structurally smaller arguments (probably in the search procedure, just ignoring invalid proofs there)
testRules2 :: HintDB
testRules2 =
  [ -- global scope
    Rule
    { ruleName = "nil"
    , ruleConclusion = con "Vec" (var "A") (con "zero")
    , rulePremises = []
    }
  , Rule
    { ruleName = "cons"
    , ruleConclusion = con "Vec" (var "A") (con "suc" (var "n"))
    , rulePremises = [var "A", con "Vec" (var "A") (var "n")]
    }
  , Rule
    { ruleName = "map"
    , ruleConclusion = con "Vec" (var "B") (var "n")
    , rulePremises = [ con "->" (var "A") (var "B"), con "Vec" (var "A") (var "n") ]
    }
  -- local scope (quantified variables have been introduced)
  -- note that we can use "f" in two ways, either as a function transforming some A into a B,
  -- or as a value of type "A -> B"
  , Rule
    { ruleName = "f"
    , ruleConclusion = con "B"
    , rulePremises = [con "A"]
    }
  , Rule "f" (con "->" (con "A") (con "B")) []
  , Rule "x" (con "A") []
  , Rule "xs" (con "Vec" (con "A") (con "n'")) []
  ]

-- | The goal corresponding to the above example, in the second clause of the map function.
-- We need to find a value of type @Vec B n'@ where @suc n' == n@.
testGoal2 :: PsTerm
testGoal2 = con "Vec" (con "B") (con "suc" (con "n'"))

-- | this generates @cons (f x) (map f xs))@ and @(map f (cons x xs))@ for the aforementioned map function,
-- the former is is correct, the latter is not making a structurally smaller call, but the algorithm itself
-- seems to work
itWorks :: [Proof]
itWorks = dfs $ cutoff 10 $ solve testGoal2 testRules2
