module Absurd where

open import Prelude

absurd : {A : Set} -> Empty -> A
absurd x = {!!}
