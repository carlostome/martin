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
zero + b = b
succ a + b = succ (a + b)

infix 4 _==_
-- | (Almost) standard definition of equality (no levels for Set)
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
trans refl q = q

-- | Also trivial, but useful for constructing other proofs later on.
cong : ∀{A B} → (f : A → B) → {x y : A} → x == y → f x == f y
cong f refl = refl

-- | Trivial
add-left-zero : ∀ {n} → 0 + n == n
add-left-zero = refl

-- | Provable with auto when given "cong" as hint
add-right-zero : (n : Nat) → n + 0 == n
add-right-zero zero = refl
add-right-zero (succ n) = cong succ (add-right-zero n)

-- | First branch needs "cong" as hint in second branch
add-right-reduce : (m n : Nat) → m + succ n == succ (m + n)
add-right-reduce zero n = refl
add-right-reduce (succ m) n = cong succ (add-right-reduce m n)

-- | Needs "sym" and "add-right-zero" as hints in first branch and
-- "sym", "trans", "cong" and "add-right-reduce" in second branch.
add-commutative : (m n : Nat) → m + n == n + m
add-commutative zero n = sym (add-right-zero n)
add-commutative (succ m) n = trans (cong succ (add-commutative m n))
                               (sym (add-right-reduce n m))

-- | Provable with "cong"
add-associative : (l m n : Nat) → (l + m) + n == l + (m + n)
add-associative zero m n = refl
add-associative (succ l) m n = cong succ (add-associative l m n)

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
{-leq-add-invariant : ∀ {l m} → (n : Nat) → l ≤ m → l + n ≤ m + n
leq-add-invariant zero p = p
leq-add-invariant (succ n) p = leq-succ (leq-add-invariant n p)
-}
-- | anti symmetry of ≤, provable by auto when given "cong" as a hint
leq-anti-sym : ∀ {m n} → m ≤ n → n ≤ m → m == n
leq-anti-sym leq-zero leq-zero = refl
leq-anti-sym (leq-succ p) (leq-succ q) = cong succ (leq-anti-sym p q)

-- | reflexivity of ≤, provable by auto after matching on "n"
leq-refl : (n : Nat) → n ≤ n
leq-refl zero = leq-zero
leq-refl (succ n) = leq-succ (leq-refl n)

-- | Provable by auto, after matching on the first argument, and the second argument in the second case
-- Note that it is not required to match on both arguments in the first case. We need to make sure not to
-- split too much.
leq-trans : ∀ {l m n} → l ≤ m → m ≤ n → l ≤ n
leq-trans leq-zero q = leq-zero
leq-trans (leq-succ p) (leq-succ q) = leq-succ (leq-trans p q)


infixr 5 _∷_
-- | Standard definition of vectors
data Vec (A : Set) : Nat → Set where
  []  : Vec A 0
  _∷_ : ∀ {n} → A → Vec A n → Vec A (succ n)

infixr 5 _++_
-- | Auto finds solution after matching first argument
_++_ : ∀{m n A} → Vec A m → Vec A n → Vec A (m + n)
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ xs ++ ys

-- | Proofsearch finds right term for foldl with this type
foldl : ∀ {n A} → (B : Nat → Set) → (∀ {m} → B (succ m) → A → B m) → B n → Vec A n → B 0
foldl B f z [] = z
foldl B f z (x ∷ xs) = foldl B f (f z x) xs

infix 4 _⊆_
data _⊆_ {A : Set} : {m n : Nat} → Vec A m → Vec A n → Set where
  sub-empty : ∀{n} {xs : Vec A n} → [] ⊆ xs
  sub-same  : ∀{m n} {xs : Vec A m} {ys : Vec A n} {x : A} → xs ⊆ ys → x ∷ xs ⊆ x ∷ ys
  sub-cons  : ∀{m n} {xs : Vec A m} {ys : Vec A n} {y : A} → xs ⊆ ys → xs ⊆ y ∷ ys

