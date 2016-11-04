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

data Empty : Set where

data Dec (A : Set) : Set where
  yes : A -> Dec A
  no : (A -> Empty) -> Dec A

data Member {A : Set} (x : A) : {n : Nat} -> Vec A n -> Set where
  here : forall {n} -> {xs : Vec A n} -> Member x (cons x xs)
  there : forall {y n} -> {xs : Vec A n} -> Member x xs -> Member x (cons y xs)

{-empty-no-member : forall {A} -> {x : A} -> Member x nil -> Empty
empty-no-member ()

neither-here-nor-there : forall {A n} -> {x y : A} {ys : Vec A n} -> (x == y -> Empty) -> (Member x ys -> Empty) -> Member x (cons y ys) -> Empty
neither-here-nor-there not-here not-there here = not-here refl
neither-here-nor-there not-here not-there (there member) = not-there member

member : forall {A n} -> ((x y : A) -> Dec (x == y)) -> (v : A) -> (vs : Vec A n) -> Dec (Member v vs)
member eq? x nil = no empty-no-member
member eq? x (cons y ys) with eq? x y
member eq? x (cons .x ys) | yes refl = yes here
member eq? x (cons y ys) | no pf with member eq? x ys
member eq? x (cons y _) | no pf | yes pm = yes (there pm)
member eq? x (cons y ys) | no pf | no pnm = no (neither-here-nor-there pf pnm)
-}

empty-no-member : forall {A} -> {x : A} -> Member x nil -> Empty
empty-no-member p = {!!}

neither-here-nor-there : forall {A n} -> {x y : A} {ys : Vec A n} -> (x == y -> Empty) -> (Member x ys -> Empty) -> Member x (cons y ys) -> Empty
neither-here-nor-there not-here not-there member = {!!}

member : forall {A n} -> ((x y : A) -> Dec (x == y)) -> (v : A) -> (vs : Vec A n) -> Dec (Member v vs)
member eq? x nil = no empty-no-member
member eq? x (cons y ys) with eq? x y
member eq? x (cons y ys) | yes p = {!!}
member eq? x (cons y ys) | no pf with member eq? x ys
member eq? x (cons y ys) | no pf | member = {!!}
