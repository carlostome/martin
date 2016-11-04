module ListAppend where

open import Prelude

append : forall {A} -> List A -> List A -> List A
append nil ys = ys
append (cons x xs) ys = cons x (append xs ys)

appendP1 : forall {x l l'} -> append (cons x l) l' == cons x (append l l')
appendP1 = refl

appendP2 : forall {l} -> append nil l == l
appendP2 = refl
