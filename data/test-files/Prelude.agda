module Prelude where

data Nat : Set where
  zero : Nat
  suc : Nat -> Nat

{-# BUILTIN NATURAL Nat #-}

data _==_ {A : Set} (x : A) : A → Set where
  refl : x == x

data Vec (A : Set) : Nat -> Set where
  nil : Vec A 0
  cons : forall {n} -> A -> Vec A n -> Vec A (suc n)

