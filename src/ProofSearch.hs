{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs             #-}
{-# LANGUAGE RankNTypes        #-}
module ProofSearch where

import           Control.Monad.State
import           Data.Functor.Const
import           Data.Map            (Map)
import qualified Data.Map            as Map
import           Data.Monoid

data VarIdent = Raw !String | Unique !String !Int
  deriving (Eq, Ord, Show, Read)
type ConIdent = String
type RuleIdent = String

makeUnique :: VarIdent -> Int -> VarIdent
makeUnique (Raw v)      = Unique v
makeUnique (Unique v _) = Unique v

data PsTerm = Var !VarIdent | Con !ConIdent [PsTerm]
  deriving (Eq, Ord, Show, Read)

variables :: Applicative f => (VarIdent -> f VarIdent) -> PsTerm -> f PsTerm
variables f = go where
  go (Var v)    = Var <$> f v
  go (Con c ts) = Con c <$> traverse go ts

listOf :: forall s t a b. (forall f. Applicative f => (a -> f b) -> s -> f t) -> s -> [a]
listOf f s = getConst $ f (Const . (:[])) s

-- | Replaces every variable in a term with a fresh variable.
freshenTerm :: PsTerm -> State (Int, Map VarIdent VarIdent) PsTerm
freshenTerm = variables $ \v -> state $ \(n, rep) ->
  case Map.lookup v rep of
    Just v' -> (v', (n, rep))
    Nothing -> let v' = makeUnique v n
               in (v', (n + 1, Map.insert v v' rep))

-- newtype Subst = Subst { substMap :: Map VarIdent PsTerm }
type Subst = Map VarIdent PsTerm

class Substitutable t => Unify t where
  unify :: t -> t -> Maybe Subst

class Substitutable t where
  subst :: Subst -> t -> t

instance Substitutable PsTerm where
  subst s = go where
    go (Var v)    = Map.findWithDefault (Var v) v s
    go (Con c ts) = Con c $ map go ts

instance Substitutable Subst where
  subst sub1 sub2 = Map.union sub1 $ fmap (subst sub1) sub2

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

data Rule = Rule
  { ruleName       :: RuleIdent
  , ruleConclusion :: PsTerm
  , rulePremises   :: [PsTerm]
  } deriving (Eq, Ord, Show, Read)

type HintDB = [Rule]

data Proof = Proof
  { proofRule :: RuleIdent
  , proofArgs :: [Proof]
  }
  deriving (Eq, Ord, Show, Read)

data PartialProof = PartialProof
  { partialProofHoles :: [PsTerm]
  , partialProofFill  :: [Proof] -> Proof
  }

data SearchTree a = Leaf a | Node [SearchTree a]
  deriving (Eq, Ord, Show, Read)

instance Functor SearchTree where
  fmap f (Leaf x)  = Leaf (f x)
  fmap f (Node xs) = Node (map (fmap f) xs)

instance Applicative SearchTree where
  pure = Leaf
  (Leaf f) <*> x = fmap f x
  (Node xs) <*> x = Node $ map (<*> x) xs

instance Monad SearchTree where
  Leaf x >>= f = f x
  Node xs >>= f = Node $ map (>>= f) xs

data SearchState = SearchState
  { freshId :: Int
  } deriving (Show)

type Search = State SearchState
type SearchT = StateT SearchState SearchTree

-- | Instantiates every variable in a rule with a fresh variable
instantiateRule :: Monad m => Rule -> StateT SearchState m Rule
instantiateRule r = state $ \st ->
  let (r', (n', _)) = runState (Rule (ruleName r) <$> freshenTerm (ruleConclusion r) <*> traverse freshenTerm (rulePremises r)) (freshId st, Map.empty)
  in (r', st { freshId = n' })

ruleArity :: Rule -> Int
ruleArity = length . rulePremises

apply :: Rule -> [Proof] -> [Proof]
apply r xs = new : rest where
  n = ruleArity r
  new = Proof (ruleName r) (take n xs)
  rest = drop n xs

solveAcc :: HintDB -> PartialProof -> SearchT Proof
solveAcc rules (PartialProof [] p) = return $ p []
solveAcc rules (PartialProof (g : gs) p) = StateT $ wrap $ map (instantiateRule >=> step) rules where
  wrap xs s = Node $ map (flip runStateT s) xs
  step r = case unify g (ruleConclusion r) of
    Nothing -> lift $ Node []
    Just mgu -> do
      let gs' = subst mgu (rulePremises r ++ gs)
          prf = PartialProof gs' (p . apply r)
      solveAcc rules prf

solve :: PsTerm -> HintDB -> SearchTree Proof
solve goal rules = evalStateT (solveAcc rules (PartialProof [goal] head)) (SearchState 0)

dfs :: Int -> SearchTree a -> [a]
dfs _ (Leaf x) = [x]
dfs n (Node xs)
  | n > 0 = concatMap (dfs (n - 1)) xs
  | otherwise = []

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

var :: String -> PsTerm
var = Var . Raw

con :: MakeCon r => ConIdent -> r
con c = con' c []

class MakeCon r where
  con' :: ConIdent -> [PsTerm] -> r

instance MakeCon PsTerm where
  con' = Con

instance (p ~ PsTerm, MakeCon r) => MakeCon (p -> r) where
  con' c ts p = con' c (ts ++ [p])

-- | The available rules in the following context
--
-- @
--   map : (A -> B) -> Vec A n -> Vec B n
--   map f nil = nil
--   map f (cons x xs) = ?
-- @
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

testGoal2 :: PsTerm
testGoal2 = con "Vec" (con "B") (con "suc" (con "n'"))

-- | this generates @cons (f x) (map f xs))@ and @(map f (cons x xs))@ for the aforementioned map function,
-- the former is is correct, the latter is not making a structurally smaller call, but the algorithm itself
-- seems to work
itWorks = map ppProof $ dfs 6 $ solve testGoal2 testRules2

ppProof :: Proof -> String
ppProof (Proof r [])   = r
ppProof (Proof r args) = "(" ++ unwords (r : map ppProof args) ++ ")"
