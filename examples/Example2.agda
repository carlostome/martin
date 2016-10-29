module Example2 where

data Nat : Set where
  zero : Nat
  succ : Nat → Nat

data _==_ {A : Set} (x : A) : A → Set where
  refl : x == x

-- id : {A : Set} -> A
-- id = {!id!}

-- prop : {A : Set} → (a : A) → id == a
-- prop _  = refl

add : Nat -> Nat -> Nat
add x y = {!!}

p1 : (n : Nat) -> add zero n == n
p1 n = refl

p2 : (n : Nat) -> (m : Nat) -> add (succ n) m == succ (add n m)
p2 n m = refl

