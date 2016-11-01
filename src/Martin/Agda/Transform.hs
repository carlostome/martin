{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeSynonymInstances  #-}
{-| This module contains several utility functions for transforming
-   Agda programs.
-}
module Martin.Agda.Transform
  ( -- * Stateful syntax transformations
    rebuildInteractionPoints
  , setMetaNumbersToInteraction
  , literalToConstructor
  , constructorFormA
  -- * Pure syntax transformations
  , flattenVisibleApp
  , replaceClauses
  , replaceHole
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
import qualified Agda.Syntax.Internal                       as I
import           Agda.Syntax.Literal
import           Agda.Syntax.Parser
import           Agda.Syntax.Position
import           Agda.Syntax.Scope.Base
import           Agda.Syntax.Scope.Monad                    as Scope
import           Agda.Syntax.Translation.AbstractToConcrete
import           Agda.Syntax.Translation.ConcreteToAbstract
import           Agda.Syntax.Translation.InternalToAbstract
import           Agda.TypeChecking.Monad
import           Agda.TypeChecking.Monad.Builtin
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

import qualified Martin.Agda.Query                          as Q

-- | Replaces all question marks with fresh interaction points and registers them with the type checker.
-- This step is necessary after resetting the type checker state.
rebuildInteractionPoints :: A.ExprLike e
                          => e -> TCM (e,[InteractionId])
rebuildInteractionPoints e = runWriterT (A.traverseExpr go e) where
  go (A.QuestionMark m ii) = do
    nii <- lift $ registerInteractionPoint noRange Nothing
    when (ii /= (-1)) $ tell [nii]
    return (A.QuestionMark m nii)
  go other = return other

-- | Replaces a hole identified by its interaction id with a new expression.
replaceHole :: A.ExprLike e => InteractionId -> A.Expr -> e -> e
replaceHole ii repl = A.mapExpr $ \e -> case e of
                                  A.QuestionMark _ iiq
                                    | iiq == ii -> repl
                                  other -> other

-- | Replaces the clause identified by the interaction id of its single RHS hole
-- with the list of new clauses.
replaceClauses :: InteractionId -> [A.Clause] -> [A.Declaration] -> [A.Declaration]
replaceClauses ii newClauses = map update where
  -- recursively traverses all declarations to replace the clauses
  update (A.Mutual mi decls) = A.Mutual mi (map update decls)
  update (A.Section mi mn bnds decls) = A.Section mi mn bnds (map update decls)
  update (A.FunDef di qn del clauses) = A.FunDef di qn del $ concatMap updateClause clauses
  update (A.RecDef di qn1 ri flag qn2 bnds e decls) = A.RecDef di qn1 ri flag qn2 bnds e (map update decls)
  update (A.ScopedDecl si decls) = A.ScopedDecl si (map update decls)
  update other = other

  updateClause cls = case A.clauseRHS cls of
    A.RHS e -> case isTopLevelHole e of
      -- the newly generated meta variables inherit the scope information of the
      -- variable they are replacing. Since we are operating on abstract syntax,
      -- which is the stage after scope checking, we need to track scope manually here.
      -- initScope updates the local variables of the old meta variable's scope
      Just (mi, hole) | hole == ii -> map (initScope $ metaScope mi) newClauses
      _ -> [cls]
    A.WithRHS qn exprs clauses ->
      let newrhs = A.WithRHS qn exprs (concatMap updateClause clauses)
      in [cls { A.clauseRHS = newrhs}]
    _ -> [cls]

  -- checks whether there is a top level hole in the expression of a clause
  isTopLevelHole (A.QuestionMark mi hole) = Just (mi, hole)
  isTopLevelHole (A.ScopedExpr _ e)       = isTopLevelHole e
  isTopLevelHole _                        = Nothing

  initScope scope clause =
    -- here we need to extract all the bound names in the patterns of the clause and insert
    -- them into the top level scope
    let locals = map (A.nameConcrete &&& LocalVar) $ clauseLocals $ A.clauseLHS clause
        newScope = scope { scopeLocals = locals }
        -- update scoped things in the expression with the new scope
        updScope (A.ScopedExpr _ e) = A.ScopedExpr newScope e
        updScope (A.QuestionMark mi hole) = A.QuestionMark mi { metaScope = newScope } hole
        updScope o = o
    in A.mapExpr updScope clause

  -- finds all local variables in a clause
  -- REMARK: currently only works for patterns, not co-patterns
  clauseLocals (A.LHS _ (A.LHSHead _ pats) wpats) = concatMap (patternDecls . namedThing . unArg) pats ++ concatMap patternDecls wpats
  clauseLocals _ = []

  -- finds all variables bound in patterns, only constructors and variables supported so far
  -- not sure what else we need, but we'll find out sooner or later
  patternDecls (A.VarP n) = [n]
  patternDecls (A.ConP _ _ a) = concatMap (patternDecls . namedThing . unArg) a
  patternDecls (A.DefP _ _ a) = concatMap (patternDecls . namedThing . unArg) a
  patternDecls _ = []


-- | In the abstract syntax, sets the 'metaNumber' of 'QuestionMark' to
-- the corresponding interaction ID to have it printed. Seems to be the suggested
-- way according to the documentation for 'QuestionMark'.
-- WARNING: This messes with the internal state of expressions which causes type checking to brake,
-- so only use before pretty printing.
setMetaNumbersToInteraction :: A.ExprLike e => e -> e
setMetaNumbersToInteraction = A.mapExpr go where
  go (A.QuestionMark meta ii) = A.QuestionMark meta { metaNumber = Just $ MetaId $ interactionId ii } ii
  go other = other


-- | This takes an expression and flattens all top level binary application constructors into a list.
-- For example, it will turn @(f x) y@ into @[f, x, y]@.
-- If there is no application, a singleton list is returned, i.e. a single @x@ is transformed into @[x]@.
-- Implicit arguments are left out.
flattenVisibleApp :: A.Expr -> [A.Expr]
flattenVisibleApp (A.App _ f x) = flattenVisibleApp f ++ [ namedThing $ unArg x | not (Q.isHiddenArg x) ]
flattenVisibleApp (A.ScopedExpr _ e) = flattenVisibleApp e
flattenVisibleApp other = [other]

-- | Converts a literal to an expression consisting of the corresponding constructors.
literalToConstructor :: Literal -> TCM (Maybe A.Expr)
literalToConstructor lit = fmap Just (constructorForm (I.Lit lit) >>= reify) `catchError` \_ -> return Nothing

-- | Converts all literals in an expression to their corresponding constructors.
constructorFormA :: A.ExprLike e => e -> TCM e
constructorFormA = A.traverseExpr $ \case
  A.Lit lit -> literalToConstructor lit >>= \case
    Nothing -> pure $ A.Lit lit
    Just c -> pure c
  other -> pure other
