module VecMember where

open import Prelude

data Member {A : Set} (x : A) : {n : Nat} -> Vec A n -> Set where
  here : forall {n} -> {xs : Vec A n} -> Member x (cons x xs)
  there : forall {y n} -> {xs : Vec A n} -> Member x xs -> Member x (cons y xs)

empty-no-member' : forall {A} -> {x : A} -> Member x nil -> Empty
empty-no-member' p = {!!}

empty-no-member : forall {A} -> {x : A} -> Not (Member x nil)
empty-no-member = is-absurd empty-no-member'

neither-here-nor-there' : forall {A n} -> {x y : A} {ys : Vec A n} -> (x == y -> Empty) -> (Member x ys -> Empty) -> Member x (cons y ys) -> Empty
neither-here-nor-there' not-here not-there member = {!!}

neither-here-nor-there : forall {A n} -> {x y : A} {ys : Vec A n} -> (x == y -> Empty) -> (Member x ys -> Empty) -> Not (Member x (cons y ys))
neither-here-nor-there not-here not-there = is-absurd (neither-here-nor-there' not-here not-there)

member? : forall {A n} -> ((x y : A) -> Dec (x == y)) -> (v : A) -> (vs : Vec A n) -> Dec (Member v vs)
member? eq? x nil = no empty-no-member
member? eq? x (cons y ys) with eq? x y
member? eq? x (cons y ys) | yes p = {!!}
member? eq? x (cons y ys) | no pf with member? eq? x ys
member? eq? x (cons y ys) | no pf | member = {!!}
