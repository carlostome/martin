module Example where

data Nat : Set where
  zero : Nat
  succ : Nat → Nat

fooadd : Nat → Nat → Nat
fooadd x zero = {!!}
fooadd x (succ y) = succ {!!}
