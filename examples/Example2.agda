module Example where

postulate
  Level : Set

-- MAlonzo compiles Level to (). This should be safe, because it is
-- not possible to pattern match on levels.

{-# COMPILED_TYPE Level () #-}
{-# BUILTIN LEVEL Level    #-}

postulate
  lzero : Level
  lsuc  : (ℓ : Level) → Level
  _⊔_   : (ℓ₁ ℓ₂ : Level) → Level

{-# BUILTIN LEVELZERO lzero #-}
{-# BUILTIN LEVELSUC  lsuc  #-}
{-# BUILTIN LEVELMAX  _⊔_   #-}

data Nat : Set where
  zero : Nat
  succ : Nat → Nat

fooadd : Nat → Nat → Nat
fooadd x zero = {!!}
fooadd x (succ y) = succ {!!}
