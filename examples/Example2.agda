module Example2 where

data Nat : Set where
  zero : Nat
  succ : Nat → Nat

data N : Set where
    z : N
    s : N -> N

data V : Set where
    v : V -> V

id : Nat -> Nat
id zero = {!!}
id (succ n) = {!!}

id2 : V -> V -> Nat
id2 n e = {!!}
