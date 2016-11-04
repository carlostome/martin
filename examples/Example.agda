module Example where

data Nat : Set where
  zero : Nat
  succ : Nat → Nat

{-# BUILTIN NATURAL Nat #-}

infixl 6 _+_
{- Proofsearch is not able to find some useful result here obviously, type is too weak

   The correct steps to solve this might still be inferrable from a teacher-given model solution:

   - The correct pattern matching in simple cases can be found by "diffing" the actual patterns with the plain definition a + b
     This approach becomes problematic whenever the order of case-splitting matters because that information might not be
     uniquely determined by just looking at the result. (FURTHER INVESTIGATION NEEDED)
-}
_+_ : Nat → Nat → Nat
a + zero = a
a + succ b = succ (a + b)

infix 4 _==_
-- | Standard definition of equality
data _==_ {A : Set} (x : A) : A → Set where
  refl : x == x

{- Trivial example, but also requires case-splitting before being able to use auto.
  Actually, this example shows another difficulty we will encounter when trying to
  implement the seach algorithm ourselves. The type of "refl" will only match the
  type of the hole after doing the pattern match, because that causes the type checker
  to internally unify "x" and "y".
  The complexity of this could get out of hand rather quickly
-}
sym : ∀ {A} {x y : A} → x == y → y == x
sym refl = refl

-- | Also trivial, but has more than one solution, depending whether one case-splits
-- just one argument or both.
trans : ∀{A} {x y z : A} → x == y → y == z → x == z
trans p refl = p

-- | Also trivial, but useful for constructing other proofs later on.
cong : ∀{A B} → (f : A → B) → {x y : A} → x == y → f x == f y
cong f refl = refl

infix 4 _≤_
-- | A relation between natural numbers
data _≤_ : Nat → Nat → Set where
  leq-zero : ∀ {n} → 0 ≤ n
  leq-succ : ∀ {m n} → m ≤ n → succ m ≤ succ n

{- ≤ is invariant under addition
   The proof search finds this proof, after manually matching on n.
   When matching on "p", it appears to be non-solvable with the current definitions in scope,
   or at least much more tedious.
   steps for constructing manually:

   - split on "n"
   - refine with p (matching type)
   - refine with leq-succ (matching type)
   - refine with recursive call
-}
leq-add-invariant : ∀ {l m} → (n : Nat) → l ≤ m → l + n ≤ m + n
leq-add-invariant zero p = p
leq-add-invariant (succ n) p = leq-succ (leq-add-invariant n p)

infixr 5 _∷_
-- | Standard definition of vectors
data Vec (A : Set) : Nat → Set where
  []  : Vec A 0
  _∷_ : ∀ {n} → A → Vec A n → Vec A (succ n)

infixr 5 _++_
_++_ : ∀{m n A} → Vec A m → Vec A n → Vec A (m + n)
[] ++ ys = {!!}
(x ∷ xs) ++ ys = {!!}

-- | Proofsearch finds right term for foldl with this type
foldl : ∀ {n A} → (B : Nat → Set) → (∀ {m} → B (succ m) → A → B m) → B n → Vec A n → B 0
foldl B f z [] = z
foldl B f z (x ∷ xs) = foldl B f (f z x) xs

infix 4 _⊆_
data _⊆_ {A : Set} : {m n : Nat} → Vec A m → Vec A n → Set where
  sub-empty : ∀{n} {xs : Vec A n} → [] ⊆ xs
  sub-same  : ∀{m n} {xs : Vec A m} {ys : Vec A n} {x : A} → xs ⊆ ys → x ∷ xs ⊆ x ∷ ys
  sub-cons  : ∀{m n} {xs : Vec A m} {ys : Vec A n} {y : A} → xs ⊆ ys → xs ⊆ y ∷ ys

