{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables   #-}
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

import qualified Agda.Syntax.Abstract                       as A
import qualified Agda.Syntax.Abstract.Views                 as A
import           Agda.Syntax.Common
import           Agda.Syntax.Info                           as I
import qualified Agda.Syntax.Internal                       as I
import           Agda.Syntax.Literal
import           Agda.Syntax.Position
import           Agda.Syntax.Scope.Base
import           Agda.Syntax.Translation.InternalToAbstract
import           Agda.TypeChecking.Monad
import           Agda.TypeChecking.Monad.Builtin
import           Agda.Utils.Monad                           hiding (ifM)

import           Control.Arrow                              ((&&&))
import           Control.Lens
import           Control.Monad.Except
import           Control.Monad.Writer
import           Data.Maybe

import qualified Martin.Agda.Lens                           as L
import qualified Martin.Agda.Query                          as Q

-- | Replaces all question marks with fresh interaction points and registers them with the type checker.
-- This step is necessary after resetting the type checker state.
rebuildInteractionPoints :: A.ExprLike e
                          => e -> TCM (e,[InteractionId])
rebuildInteractionPoints = runWriterT . traverseOf (L.questionMarks . _2) go where
  go ii = do
    nii <- lift $ registerInteractionPoint noRange Nothing
    when (ii /= (-1)) $ tell [nii]
    return nii

-- | Replaces a hole identified by its interaction id with a new expression.
replaceHole :: A.ExprLike e => InteractionId -> A.Expr -> e -> e
replaceHole ii repl = L.interactionPoint ii .~ repl

-- | Replaces the clause identified by the interaction id of its single RHS hole
-- with the list of new clauses.
replaceClauses :: InteractionId -> [A.Clause] -> [A.Declaration] -> [A.Declaration]
replaceClauses ii newClauses = iover L.splitClauses update where
  update (miq, iiq) cls
    | iiq == ii = map (initScope $ metaScope miq) newClauses
    | otherwise = [cls]

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
  clauseLocals (A.LHS _ (A.LHSHead _ pats) wpats) = toListOf (traversed . L._unArg . L._namedThing . L.patternVars) pats
    ++ toListOf (traversed . L.patternVars) wpats
  clauseLocals _ = []

-- | In the abstract syntax, sets the 'metaNumber' of 'QuestionMark' to
-- the corresponding interaction ID to have it printed. Seems to be the suggested
-- way according to the documentation for 'QuestionMark'.
-- WARNING: This messes with the internal state of expressions which causes type checking to brake,
-- so only use before pretty printing.
setMetaNumbersToInteraction :: A.ExprLike e => e -> e
setMetaNumbersToInteraction = over L.questionMarks $
  \(meta, ii) -> (meta { metaNumber = Just $ MetaId $ interactionId ii }, ii)


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
constructorFormA = traverseOf L.literals' $ \lit -> fromMaybe (A.Lit lit) <$> literalToConstructor lit
