module Example3 where

data List (A : Set) : Set where
  nil  : List A
  cons : A → List A → List A

data _==_ {A : Set} (a : A) : A -> Set where
  refl : a == a

cong : forall {A B} -> (f : A -> B) -> {x y : A} -> x == y -> f x == f y
cong f refl = refl

map : {A B : Set} → (A -> B) → List A -> List B
map f xs = {!!}

id : {A : Set} → A → A
id x = x

pr : forall {A} {xs : List A} → map id xs == xs
pr {xs = nil} = refl
pr {xs = cons x xs} = cong (cons x) pr
