{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes            #-}
{-| This module defines several lenses for working with Agda syntax -}
module Martin.Agda.Lens where

import qualified Agda.Syntax.Abstract                       as A
import qualified Agda.Syntax.Abstract.Views                 as A
import           Agda.Syntax.Common
import           Agda.Syntax.Info
import           Agda.Syntax.Literal

import           Control.Lens
import           Data.Generics.Geniplate

-- | A generic lens to fold over universes.
universeBiFold :: UniverseBi s t => Fold s t
universeBiFold = to universeBi . folded

-- | Information contained in a question mark AST node.
type QuestionMark = (MetaInfo, InteractionId)

-- | Only focuses on the question mark when the ID matches.
filterId :: (Choice p, Applicative f) => InteractionId -> Optic' p f QuestionMark QuestionMark
filterId ii = filtered (\q -> snd q == ii)

-- | A prism for accessing the question mark in abstract syntax
_QuestionMark :: Prism' A.Expr QuestionMark
_QuestionMark = prism' (uncurry A.QuestionMark) $ \e -> case e of
  A.QuestionMark mi ii -> Just (mi, ii)
  _                    -> Nothing

-- | A prism for replacing a question mark with an expression.
_QuestionMark' :: Prism A.Expr A.Expr QuestionMark A.Expr
_QuestionMark' = prism id $ \e -> case e of
  A.QuestionMark mi ii -> Right (mi, ii)
  other                -> Left other

-- | A traversal over all question marks in the AST.
questionMarks :: A.ExprLike e => Traversal' e QuestionMark
questionMarks f = A.recurseExpr go where
  go (A.QuestionMark mi ii) _ = uncurry A.QuestionMark <$> f (mi,ii)
  go _ post                   = post

-- | A traversal over all question marks in the AST that can replace them
--   with arbitrary expressions.
questionMarks' :: A.ExprLike e => Traversal e e QuestionMark A.Expr
questionMarks' f = A.recurseExpr go where
  go (A.QuestionMark mi ii) _ = f (mi,ii)
  go _ post                   = post

-- | A traversal focusing on all question marks with the given id.
--   When passed a valid syntax tree, only one such question mark should exist.
interactionPoint :: A.ExprLike e => InteractionId -> Traversal e e QuestionMark A.Expr
interactionPoint ii  f = A.recurseExpr go where
  go (A.QuestionMark mi iiq) _
    | ii == iiq = f (mi, iiq)
  go _ post     = post

-- | Traverses all literals in an AST.
literals :: A.ExprLike e => Traversal' e Literal
literals f = A.recurseExpr go where
  go (A.Lit lit) _ = A.Lit <$> f lit
  go _ post        = post

-- | Traverses all literals in an AST to replace them with an arbitrary expression.
literals' :: A.ExprLike e => Traversal e e Literal A.Expr
literals' f = A.recurseExpr go where
  go (A.Lit lit) _ = f lit
  go _ post        = post


_unArg :: Lens (Arg e) (Arg e') e e'
_unArg = lens unArg (\a e -> a { unArg = e} )

_namedThing :: Lens (Named n a) (Named n a') a a'
_namedThing = lens namedThing (\n a -> n { namedThing = a })

-- | Traversal of all variables in a pattern.
patternVars :: Traversal' (A.Pattern' e) A.Name
patternVars f = go where
  go (A.VarP n) = A.VarP <$> f n
  go (A.ConP info name a) = A.ConP info name <$> traverseOf (traversed . _unArg . _namedThing) go a
  go (A.DefP info name a) = A.DefP info name <$> traverseOf (traversed . _unArg . _namedThing) go a
  go other = pure other

-- | A lens that skips top-level scoped expressions.
skipScoped :: Lens' A.Expr A.Expr
skipScoped f = go where
  go (A.ScopedExpr s e) = A.ScopedExpr s <$> go e
  go other              = f other

class HasClauses a where
  -- | Traverses all clauses that have an actual RHS.
  rhsClauses :: Traversal' a A.Clause
  -- | Traverses all clauses that have an actual RHS and allows replacing them with multiple.
  splitClauses :: IndexedTraversal QuestionMark a a A.Clause [A.Clause]

instance HasClauses A.Declaration where
  rhsClauses f = go where
    go (A.Mutual m decls)             = A.Mutual m <$> traverse go decls
    go (A.Section a b c decls)        = A.Section a b c <$> traverse go decls
    go (A.RecDef a b c d e g h decls) = A.RecDef a b c d e g h <$> traverse go decls
    go (A.ScopedDecl s decls)         = A.ScopedDecl s <$> traverse go decls
    go (A.FunDef a b c cls)           = A.FunDef a b c <$> traverse goClause cls
    go other                          = pure other

    goClause cls = checkRHS (A.clauseRHS cls) cls
    checkRHS (A.RHS _) cls = f cls
    checkRHS A.AbsurdRHS cls = f cls
    checkRHS (A.WithRHS q e cls') cls = (\c -> cls { A.clauseRHS = A.WithRHS q e c }) <$> traverse goClause cls'
    checkRHS (A.RewriteRHS _ r _) cls = checkRHS r cls

  splitClauses f = go where
    go (A.Mutual m decls)             = A.Mutual m <$> traverse go decls
    go (A.Section a b c decls)        = A.Section a b c <$> traverse go decls
    go (A.RecDef a b c d e g h decls) = A.RecDef a b c d e g h <$> traverse go decls
    go (A.ScopedDecl s decls)         = A.ScopedDecl s <$> traverse go decls
    go (A.FunDef a b c cls)           = A.FunDef a b c . concat <$> traverse goClause cls
    go other                          = pure other

    goClause cls = checkRHS (A.clauseRHS cls) cls
    checkRHS (A.RHS e) cls = case preview (skipScoped . _QuestionMark) e of
      Nothing -> pure [cls]
      Just qm -> indexed f qm cls
    checkRHS A.AbsurdRHS cls = pure [cls]
    checkRHS (A.WithRHS q e cls') cls = (\c -> [cls { A.clauseRHS = A.WithRHS q e c }]) . concat <$> traverse goClause cls'
    checkRHS (A.RewriteRHS _ r _) cls = checkRHS r cls

instance (HasClauses a) => HasClauses [a] where
  rhsClauses = traversed . rhsClauses
  splitClauses = traversed . splitClauses

-- | Traverses the RHS expression of a clause, if it exists.
rhs :: Traversal' A.Clause A.Expr
rhs f cls = case A.clauseRHS cls of
  A.RHS e -> (\r -> cls { A.clauseRHS = A.RHS r }) <$> f e
  _       -> pure cls
