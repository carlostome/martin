module VecAppend where

open import Prelude

add : Nat -> Nat -> Nat
add zero y = y
add (suc x) y = suc (add x y)

append : forall {A m n} -> Vec A m -> Vec A n -> Vec A (add m n)
append xs ys = {!!}
