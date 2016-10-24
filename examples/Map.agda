module Map where

data Nat : Set where
  zero : Nat
  suc : Nat -> Nat

{-# BUILTIN NATURAL Nat #-}

data Vec (A : Set) : Nat -> Set where
  nil : Vec A 0
  cons : forall {n} -> A -> Vec A n -> Vec A (suc n)

map : forall {A B n} -> (A -> B) -> Vec A n -> Vec B n
map f nil = {!!}
map f (cons x xs) = {!!}
