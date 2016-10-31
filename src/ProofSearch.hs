{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs             #-}
{-# LANGUAGE RankNTypes        #-}
{-# LANGUAGE DeriveGeneric     #-}
module ProofSearch where

import           Control.Monad.State
import           Data.Functor.Const
import           Data.Map            (Map)
import qualified Data.Map            as Map
import           Control.DeepSeq
import           GHC.Generics

import SearchTree

-- | The type of variable identifiers. In contrast to the paper,
-- this implementation currently relies on human readable strings.
-- For one, it can make the state of the proof search more easy to read,
-- but they are also easier to keep track of, lacking the advanced features
-- of Agda's type system.
data VarIdent
  = Raw !String
  -- ^ a raw variable name as it is occurring in the input
  | Unique !String !Int
  -- ^ a variable name that has been made fresh by pairing it with a unique integer.
  -- These identifiers should not be created manually.
  deriving (Eq, Ord, Show, Read, Generic)

instance NFData VarIdent
instance NFData PsTerm
instance NFData Rule

type ConIdent = String
type RuleIdent = String

-- | Pairs a raw name with a number or replaces the number of a unique name.
makeUnique :: VarIdent -> Int -> VarIdent
makeUnique (Raw v)      = Unique v
makeUnique (Unique v _) = Unique v

-- | A term in the proof search.
data PsTerm
  = Var !VarIdent          -- ^ a proof-variable (i.e. a universally quantified type variable)
  | Con !ConIdent [PsTerm] -- ^ a (type) constructor with a name and some arguments
  deriving (Eq, Ord, Show, Read, Generic)

-- | A traversal of variables in a term. (type is compatible with lens)
variables :: Applicative f => (VarIdent -> f VarIdent) -> PsTerm -> f PsTerm
variables f = go where
  go (Var v)    = Var <$> f v
  go (Con c ts) = Con c <$> traverse go ts

-- | Returns a list of all elements targeted by a traversal.
listOf :: forall s t a b. (forall f. Applicative f => (a -> f b) -> s -> f t) -> s -> [a]
listOf f s = getConst $ f (Const . (:[])) s

-- | Replaces every variable in a term with a fresh variable.
freshenTerm :: PsTerm -> State (Int, Map VarIdent VarIdent) PsTerm
freshenTerm = variables $ \v -> state $ \(n, rep) ->
  case Map.lookup v rep of
    Just v' -> (v', (n, rep))
    Nothing -> let v' = makeUnique v n
               in (v', (n + 1, Map.insert v v' rep))

-- | A substitution maps variables to terms.
type Subst = Map VarIdent PsTerm

class Substitutable t => Unify t where
  unify :: t -> t -> Maybe Subst

class Substitutable t where
  subst :: Subst -> t -> t

instance Substitutable PsTerm where
  subst s = go where
    go (Var v)    = Map.findWithDefault (Var v) v s
    go (Con c ts) = Con c $ map go ts

-- | Standard implementation of unification.
instance Unify PsTerm where
  unify (Var u) (Var v)
    | u == v    = Just Map.empty
    | otherwise = Just $ Map.singleton v (Var u)
  unify (Con c1 xs) (Con c2 ys)
    | c1 == c2  = unify xs ys
    | otherwise = Nothing
  unify (Var v) c@Con{}
    | v `notElem` listOf variables c = Just $ Map.singleton v c
  unify c@Con{} v@Var{} = unify v c
  unify _ _ = Nothing

instance Substitutable a => Substitutable [a] where
  subst s = map (subst s)

instance Unify a => Unify [a] where
  unify [] [] = Just Map.empty
  unify (x:xs) (y:ys) = do
    sub <- unify xs ys
    sub' <- unify (subst sub x) (subst sub y)
    return $ subst sub' sub
  unify _ _ = Nothing

instance Substitutable Subst where
  subst sub1 sub2 = Map.union sub1 $ fmap (subst sub1) sub2

-- | A rule is defined similar to Prolog, with a conclusion that follows from a list
-- of premises that all need to be satisfied.
-- The rule name is used to be able to later reconstruct the steps taken for the proof.
data Rule = Rule
  { ruleName       :: RuleIdent
  , ruleConclusion :: PsTerm
  , rulePremises   :: [PsTerm]
  } deriving (Eq, Ord, Show, Read, Generic)

-- | A hint database is simply a list of rules that can be applied.
type HintDB = [Rule]

-- | A proof for a rule, containing proofs for the rules premises as well.
data Proof = Proof
  { proofRule :: RuleIdent
  -- ^ the rule that is proved by this proof
  , proofArgs :: [Proof]
  -- ^ the proofs of the premises of the rule
  , proofTerm :: PsTerm
  -- ^ the term being proven on this level
  -- REMARK: added this field to allow caching of intermediate results, if somehow feasible
  }
  deriving (Eq, Ord, Show, Read)

-- | A partial proof is a list of subgoals together with a function creating a proof of the goal
-- from the proofs of the subgoals.
data PartialProof = PartialProof
  { partialProofHoles :: [PsTerm]
  -- ^ the sub goals that still need to be proven
  , partialProofFill  :: [Proof] -> Proof
  -- ^ a function generating a proof from the proofs of the subgoals
  }

-- | The internal state of the proof search.
data SearchState = SearchState
  { freshId :: Int
  -- ^ a counter providing fresh names for variables.
  } deriving (Show)

type Search = State SearchState
type SearchT = StateT SearchState SearchTree

-- | Instantiates every variable in a rule with a fresh variable.
instantiateRule :: Monad m => Rule -> StateT SearchState m Rule
instantiateRule r = state $ \st ->
  let (r', (n', _)) = runState (Rule (ruleName r) <$> freshenTerm (ruleConclusion r) <*> traverse freshenTerm (rulePremises r)) (freshId st, Map.empty)
  in (r', st { freshId = n' })

-- | The arity of a rule is the number of its premises.
ruleArity :: Rule -> Int
ruleArity = length . rulePremises

-- | Applies a rule of arity @n@ to a list of proof by using the first @n@ proofs
-- as proofs for its premises, and replacing them with a proof of the rule itself.
-- The remaining proofs are not modified.
apply :: PsTerm -> Rule -> [Proof] -> [Proof]
apply goal r xs = new : rest where
  n = ruleArity r
  new = Proof (ruleName r) (take n xs) goal
  rest = drop n xs

-- | Solves a partial proof given a set of rules.
solveAcc :: HintDB -> PartialProof -> SearchT Proof
solveAcc _     (PartialProof [] p) = return $ p [] -- no goals left
solveAcc rules (PartialProof (g : gs) p) =
  StateT $ wrap $ map (instantiateRule >=> step) rules where
  -- wraps all stateful branches in a node
  wrap xs s = Node $ map (`runStateT` s) xs
  -- tries to apply a single rule
  step r = case unify g (ruleConclusion r) of
    -- cannot unify rules conclusion with the goal
    Nothing -> lift $ Node [] -- failure
    -- conclusion was unified
    Just mgu -> do
      -- apply substitution to remaining goals and add the rules premises as new goals
      let gs' = subst mgu (rulePremises r ++ gs)
      -- build new partial proof with the new list of goals
          prf = PartialProof gs' (p . apply g r)
      -- solve recursively
      solveAcc rules prf

solve :: PsTerm -> HintDB -> SearchTree Proof
solve goal rules = evalStateT (solveAcc rules (PartialProof [goal] head)) (SearchState 0)

-- this is just some test

-- | Example set of rules corresponding to the following Prolog facts
--
-- @
--   add(zero, x, x).
--   add(suc(x),y,suc(z)) :- add(x,y,z).
-- @
testRules :: HintDB
testRules =
  [ Rule
    { ruleName = "AddBase"
    , ruleConclusion = Con "add" [Con "zero" [], Var (Raw "x"), Var (Raw "x")]
    , rulePremises = []
    }
  , Rule
    { ruleName = "AddStep"
    , ruleConclusion = Con "add" [Con "suc" [Var (Raw "x")], Var (Raw "y"), Con "suc" [Var (Raw "z")]]
    , rulePremises = [Con "add" [Var (Raw "x"), Var (Raw "y"), Var (Raw "z")]]
    }
  ]

-- some helper functions to slightly ease the pain of writing these expressions by hand

-- | returns a term consisting of a raw variable
var :: String -> PsTerm
var = Var . Raw

-- | A varargs function returning a constructor term with the arguments being supplied.
con :: MakeCon r => ConIdent -> r
con c = con' c []

-- | Implementation detail of the varargs @con@ function.
class MakeCon r where
  con' :: ConIdent -> [PsTerm] -> r

instance MakeCon PsTerm where
  con' = Con

instance (p ~ PsTerm, MakeCon r) => MakeCon (p -> r) where
  con' c ts p = con' c (ts ++ [p])

ppProof :: Proof -> String
ppProof (Proof r [] g)   = "(" ++ r ++ " : " ++ show g ++ ")"
ppProof (Proof r args g) = "(" ++ unwords (r : map ppProof args) ++ " : " ++ show g ++ ")"

proofToStr :: Proof -> String
proofToStr (Proof r [] _ )  = r
proofToStr (Proof r args g) = "(" ++ unwords (r : map proofToStr args) ++ ")"
