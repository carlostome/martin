module Vec where

data Nat : Set where
  zero : Nat
  suc : Nat -> Nat

{-# BUILTIN NATURAL Nat #-}

data _==_ {A : Set} (x : A) : A → Set where
  refl : x == x

data Vec (A : Set) : Nat -> Set where
  nil : Vec A 0
  cons : forall {n} -> A -> Vec A n -> Vec A (suc n)

add : Nat -> Nat -> Nat
add zero y = y
add (suc x) y = suc (add x y)

map : forall {A B n} -> (A -> B) -> Vec A n -> Vec B n
map f xs = {!!}

replicate : forall {A} -> (n : Nat) -> A -> Vec A n
replicate count x = {!!}

append : forall {A m n} -> Vec A m -> Vec A n -> Vec A (add m n)
append xs ys = {!!}
