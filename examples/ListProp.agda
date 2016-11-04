module ListProp where

data Nat : Set where
  zero : Nat
  succ : Nat → Nat

data _==_ {A : Set} (x : A) : A → Set where
  refl : x == x

cong : ∀ {A B : Set}{a b} -> (f : A -> B) -> a == b -> f a == f b
cong f refl = refl

data List (A : Set) : Set where
  nil : List A
  cons : A -> List A -> List A

cong-succ : {x y : Nat} -> x == y -> succ x == succ y
cong-succ refl = refl

add : Nat -> Nat -> Nat
add zero y = y
add (succ x) y = succ (add x y)

map : ∀ {A B} -> (A -> B) -> List A -> List B
map f xs = ?

map-ex : map (\x -> x) (cons zero nil) == cons zero nil
map-ex = refl

map-ex2 : map (\x -> x) (cons (succ zero) (cons zero nil)) == (cons (succ zero) (cons zero nil))
map-ex2 = refl

map-ex3 : map (add (succ zero)) (cons zero nil) == cons (succ zero) nil
map-ex3 = refl
