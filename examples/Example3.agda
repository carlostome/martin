module Example3 where

data List (A : Set) : Set where
  nil  : List A
  cons : A → List A → List A

data _==_ {A : Set} (a : A) : A -> Set where
  refl : a == a

map : {A B : Set} → (A -> B) → List A -> List B
map f xs = {!!}

id : {A : Set} → A → A
id x = {!!}

pr : ∀ {xs} → map id xs == xs
pr = refl
