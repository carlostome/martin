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

data List (A : Set) : Set where
  nil : List A
  cons : A -> List A -> List A

data Empty : Set where

data Not (A : Set) : Set where
  is-absurd : (A -> Empty) -> Not A

data Dec (A : Set) : Set where
  yes : A -> Dec A
  no : Not A -> Dec A
