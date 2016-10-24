module Example2 where

postulate
    Level : Set

{-# COMPILED_TYPE Level () #-}
{-# BUILTIN LEVEL Level #-}

postulate
 lzero : Level
 lsuc  : (ℓ : Level) → Level
 _⊔_   : (ℓ₁ ℓ₂ : Level) → Level
 
{-# BUILTIN LEVELZERO lzero #-}
{-# BUILTIN LEVELSUC  lsuc  #-}
{-# BUILTIN LEVELMAX  _⊔_   #-}

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

data N : Set where
    z : N
    s : N -> N

data V : Set where
    v : V -> V

id : Nat -> Nat
id d = d

id2 : V -> V -> Nat
id2 n e = {!!}