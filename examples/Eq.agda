module Eq where

data Nat : Set where
  zero : Nat
  succ : Nat → Nat

data _==_ {A : Set} (x : A) : A → Set where
  refl : x == x

sym : forall {A} {x y : A} -> x == y -> y == x
sym n = {!!}

trans : forall {A} {x y z : A} -> x == y -> y == z -> x == z
trans n xs = {!!}

-- only specialized congruences can be used in the proof-search, because
-- the general version has a higher order application of a variable
cong-succ : {x y : Nat} -> x == y -> succ x == succ y
cong-succ n = {!!}
