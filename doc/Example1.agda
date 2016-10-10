module Example1 where

data Nat : Set where
  zero : Nat
  suc : Nat -> Nat

{-# BUILTIN NATURAL Nat #-}

data _==_ {l} {a : Set l} : a -> a -> Set l where
  refl : ∀{x} -> x == x

{-# BUILTIN EQUALITY _==_ #-}

cong : ∀{l} -> {A B : Set l} {x y : A} -> (f : A -> B) -> x == y -> f x == f y
cong f refl = refl

sym : ∀{l} {A : Set l} {x y : A} -> x == y -> y == x
sym refl = refl

_+_ : Nat -> Nat -> Nat
x + zero = x
x + suc y = suc (x + y)

_+₂_ : Nat -> Nat -> Nat
zero +₂ y = y
suc x +₂ y = {!!}

plus-right-identity : ∀{n} -> (n + 0) == n
plus-right-identity {n} = refl

plus-left-identity : (n : Nat) -> (0 + n) == n
plus-left-identity zero = refl
plus-left-identity (suc n) = cong suc (plus-left-identity n)

plus-comm : (m n : Nat) -> (m + n) == (n + m)
plus-comm m zero = sym (plus-left-identity m)
plus-comm m (suc n) = {!!}

plus-succ : ∀{m n} -> (m + suc n) == suc (m + n)
plus-succ = refl

data Vec (A : Set) : Nat -> Set where
  []  : Vec A 0
  _∷_ : ∀{n} -> A -> Vec A n -> Vec A (suc n)

replicate : ∀{A} -> (n : Nat) -> A -> Vec A n
replicate zero x = []
replicate (suc n) x = x ∷ replicate n x

data Pair (A B : Set) : Set where
  _,_ : A -> B -> Pair A B

zip : ∀{n A B} -> Vec A n -> Vec B n -> Vec (Pair A B) n
zip [] ys = []
zip {suc n} (x ∷ xs) (y ∷ ys) = replicate (suc n) (x , y)

map : ∀{n A B} -> (A -> B) -> Vec A n -> Vec B n
map f [] = []
map {suc n} f (x ∷ xs) = (f x) ∷ (map f xs) -- f x ∷ map f xs -- replicate (suc n) (f x)

id : {A : Set} -> A -> A
id x = x

map-id : ∀{n A} (xs : Vec A n) -> map id xs == xs
map-id [] = refl
map-id (x ∷ xs) = cong (_∷_ x) (map-id xs)

data Bool : Set where
  false true : Bool

not : Bool -> Bool
not false = true
not true = false

not-self-inverse : {x : Bool} -> not (not x) == x
not-self-inverse {false} = refl
not-self-inverse {true} = refl

data Empty : Set where

not-not-id : {x : Bool} -> not x == id x -> Empty
not-not-id {false} ()
not-not-id {true} ()
