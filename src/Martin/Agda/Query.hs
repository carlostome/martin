{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TemplateHaskell       #-}
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

import qualified Agda.Interaction.BasicOps                  as B
import           Agda.Interaction.FindFile
import           Agda.Interaction.Imports
import           Agda.Interaction.Options
import qualified Agda.Interaction.Options.Lenses            as Lens
import qualified Agda.Syntax.Abstract                       as A
import qualified Agda.Syntax.Abstract.Views                 as A
import           Agda.Syntax.Common
import qualified Agda.Syntax.Concrete                       as C
import           Agda.Syntax.Info                           as I
import           Agda.Syntax.Parser
import           Agda.Syntax.Position
import           Agda.Syntax.Scope.Base
import           Agda.Syntax.Scope.Monad                    as Scope
import           Agda.Syntax.Translation.AbstractToConcrete
import           Agda.Syntax.Translation.ConcreteToAbstract
import           Agda.TypeChecking.Monad
import           Agda.Utils.FileName
import           Agda.Utils.Monad                           hiding (ifM)
import qualified Agda.Utils.Trie                            as Trie

import           Control.Arrow                              ((&&&))
import           Control.Lens
import           Control.Monad.Except
import           Control.Monad.State.Strict
import           Control.Monad.Writer
import           Data.Generics.Geniplate
import qualified Data.Map.Strict                            as Map
import qualified Data.Set                                   as Set
import           System.FilePath                            ((</>))

-- | Check if the Hole is in a top level position.
checkTopLevel :: InteractionId -> [A.Declaration] -> Bool
checkTopLevel ii = any look
  where
    look (A.Mutual _ decls)             = any look decls
    look (A.Section _ _ _ decls)        = any look decls
    look (A.RecDef _ _ _ _ _ _ _ decls) = any look decls
    look (A.ScopedDecl _ decls)         = any look decls
    look (A.FunDef _ _ _ clauses)       = any lookClause clauses
    look _                              = False

    lookClause cls = case A.clauseRHS cls of
      A.RHS e -> isTopLevelHole e
      _       -> False

    isTopLevelHole (A.QuestionMark _ hole) = ii == hole
    isTopLevelHole (A.ScopedExpr _ e)      = isTopLevelHole e
    isTopLevelHole _                       = False

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
