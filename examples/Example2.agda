module Example where

data Nat : Set where
  zero : Nat
  succ : Nat → Nat

fooadd : Nat → Nat → Nat
fooadd x zero = {!0!}
fooadd x (succ y) = succ {!0!}
