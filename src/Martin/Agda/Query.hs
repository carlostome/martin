{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeSynonymInstances  #-}
{-| This module contains several utility functions for querying the
-   Agda state.
-}
module Martin.Agda.Query
  ( checkTopLevel
  , thingsInScopeWithType
  , varsInScope
  , isHiddenArg
  ) where

import qualified Agda.Interaction.BasicOps as B
import qualified Agda.Syntax.Abstract      as A
import           Agda.Syntax.Common
import           Agda.Syntax.Scope.Base
import           Agda.TypeChecking.Monad

import           Control.Lens
import qualified Data.Set                  as Set

import qualified Martin.Agda.Lens          as L

-- | Check if the Hole is in a top level position.
checkTopLevel :: InteractionId -> [A.Declaration] -> Bool
checkTopLevel ii = has (traversed . L.rhsClauses . L.rhs . L.skipScoped . L._QuestionMark . L.filterId ii)

-- | Returns everything that is in scope at a given interaction point.
-- The first A.Expr is either a Var referring to a local bound variable
-- or a Def referring to a global definition.
-- The second A.Expr is the type of that thing.
thingsInScopeWithType :: InteractionId -> TCM [(Either A.Name A.QName, A.Expr)]
thingsInScopeWithType ii = do
  m <- lookupInteractionId ii
  mi <- lookupMeta m
  let s = getMetaScope mi
      locals = map (localVar . snd) $ scopeLocals s
      globals = Set.toList $ scopeInScope s
      allExprs = map A.Var locals ++ map A.Def globals
  types <- mapM (B.typeInMeta ii B.Normalised) allExprs
  let stuffWithTypes = zip (map Left locals ++ map Right globals) types
  return stuffWithTypes

-- | Returns the local variables that are in scope at a hole.
varsInScope :: InteractionId -> TCM [A.Name]
varsInScope ii = do
  m <- lookupInteractionId ii
  mi <- lookupMeta m
  let s = getMetaScope mi
      locals = map (localVar . snd) $ scopeLocals s
  return locals

-- | Checks whether an argument is implicit.
isHiddenArg :: Arg a -> Bool
isHiddenArg arg = argInfoHiding (argInfo arg) == Hidden
