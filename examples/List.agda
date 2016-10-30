module List where

data Nat : Set where
  zero : Nat
  succ : Nat → Nat

data _==_ {A : Set} (x : A) : A → Set where
  refl : x == x

data List (A : Set) : Set where
  nil : List A
  cons : A -> List A -> List A

cong-succ : {x y : Nat} -> x == y -> succ x == succ y
cong-succ refl = refl

add : Nat -> Nat -> Nat
add zero y = y
add (succ x) y = succ (add x y)

length : forall {A} -> List A -> Nat
length nil = zero
length (cons x xs) = succ (length xs)

append : forall {A} -> List A -> List A -> List A
append xs ys = {!!}

append-unit : forall {A} -> (xs : List A) -> append nil xs == xs
append-unit xs = refl

append-cons : forall {A} -> (xs ys : List A) -> add (length xs) (length ys) == length (append xs ys)
append-cons nil ys = refl
append-cons (cons x xs) ys = cong-succ (append-cons xs ys)


