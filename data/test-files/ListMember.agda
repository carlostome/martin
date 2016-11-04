module ListMember where

open import Prelude

data Member {A : Set} (x : A) : List A -> Set where
  here : {xs : List A} -> Member x (cons x xs)
  there : forall {y} -> {xs : List A} -> Member x xs -> Member x (cons y xs)

empty-no-member' : forall {A} -> {x : A} -> Member x nil -> Empty
empty-no-member' p = {!!}

empty-no-member : forall {A} -> {x : A} -> Not (Member x nil)
empty-no-member = is-absurd empty-no-member'

neither-here-nor-there' : forall {A} -> {x y : A} {ys : List A} -> (x == y -> Empty) -> (Member x ys -> Empty) -> Member x (cons y ys) -> Empty
neither-here-nor-there' not-here not-there member = {!!}

neither-here-nor-there : forall {A} -> {x y : A} {ys : List A} -> Not (x == y) -> Not (Member x ys) -> Not (Member x (cons y ys))
neither-here-nor-there (is-absurd not-here) (is-absurd not-there) = is-absurd (neither-here-nor-there' not-here not-there)

member : forall {A} -> ((x y : A) -> Dec (x == y)) -> (v : A) -> (vs : List A) -> Dec (Member v vs)
member eq? x nil = no empty-no-member
member eq? x (cons y ys) with eq? x y
member eq? x (cons y ys) | yes p = {!!}
member eq? x (cons y ys) | no pf with member eq? x ys
member eq? x (cons y ys) | no pf | member = {!!}
