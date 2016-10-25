module Example2 where

data Nat : Set where
  zero : Nat
  succ : Nat → Nat

data _==_ {A : Set} (x : A) : A → Set where
  refl : x == x


add : Nat -> Nat -> Nat
add x y = {!!}

p1 : (n : Nat) -> add zero n == zero
p1 n = refl

