{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeSynonymInstances  #-}
module AgdaUtil
  ( -- * Program manipulation
    rebuildInteractionPoints
  , replaceClauses
  , replaceHole
  , parseAgdaFile
  , setMetaNumbersToInteraction
  -- * Information
  , checkTopLevel
  , thingsInScopeWithType
  , varsInScope
  -- * Managing Agda state
  , initAgda
  ) where

import qualified Agda.Interaction.BasicOps       as B
import           Agda.Interaction.FindFile
import           Agda.Interaction.Imports
import           Agda.Interaction.Options
import qualified Agda.Interaction.Options.Lenses as Lens
import qualified Agda.Syntax.Abstract            as A
import qualified Agda.Syntax.Abstract.Views      as A
import           Agda.Syntax.Common
import qualified Agda.Syntax.Concrete            as C
import           Agda.Syntax.Info                as I
import           Agda.Syntax.Parser
import           Agda.Syntax.Position
import           Agda.Syntax.Scope.Base
import           Agda.TypeChecking.Monad
import           Agda.Utils.FileName
import           Agda.Utils.Monad                hiding (ifM)
import qualified Agda.Utils.Trie                 as Trie

import           Control.Arrow                   ((&&&))
import           Control.Monad.Except
import           Control.Monad.State.Strict
import           Control.Monad.Writer
import qualified Data.Set                        as Set
import           System.FilePath                 ((</>))

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

-- | This initializes the TCM state just enough to get everything started.
-- For now, it uses the default options and loads Agda's Level primitives.
initAgda :: Int -> TCM TCState
initAgda verbosity = do
  -- initialize interactive state
  resetAllState
  setCommandLineOptions defaultOptions
    { optPragmaOptions = (optPragmaOptions defaultOptions)
      { optVerbose = Trie.singleton [] verbosity }
    }

  -- ==================== BEGIN CODE FROM AGDA SOURCE
  libdir <- liftIO defaultLibDir
  -- To allow posulating the built-ins, check the primitive module
  -- in unsafe mode
  _ <- bracket_ (gets Lens.getSafeMode) Lens.putSafeMode $ do
    Lens.putSafeMode False
    -- Turn off import-chasing messages.
    -- We have to modify the persistent verbosity setting, since
    -- getInterface resets the current verbosity settings to the persistent ones.
    bracket_ (gets Lens.getPersistentVerbosity) Lens.putPersistentVerbosity $ do
      Lens.modifyPersistentVerbosity (Trie.delete [])  -- set root verbosity to 0
      -- We don't want to generate highlighting information for Agda.Primitive.
      withHighlightingLevel None $ do
        primitiveModule <- moduleName $ mkAbsolute $
            libdir </> "prim" </> "Agda" </> "Primitive.agda"
        getInterface_ primitiveModule
  -- ==================== END CODE FROM AGDA SOURCE
  -- return with state right after initialization, to be able to speed up things when we need to reset
  get

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

-- | Parse an Agda file to concrete syntax.
parseAgdaFile :: FilePath -> IO (AbsolutePath, [C.Declaration])
parseAgdaFile path = do
  absPath            <- absolute path
  (_, module') <- parseFile' moduleParser absPath
  return (absPath, module')

-- | In the abstract syntax, sets the 'metaNumber' of 'QuestionMark' to
-- the corresponding interaction ID to have it printed. Seems to be the suggested
-- way according to the documentation for 'QuestionMark'.
-- WARNING: This messes with the internal state of expressions which causes type checking to brake,
-- so only use before pretty printing.
setMetaNumbersToInteraction :: A.ExprLike e => e -> e
setMetaNumbersToInteraction = A.mapExpr go where
  go (A.QuestionMark meta ii) = A.QuestionMark meta { metaNumber = Just $ MetaId $ interactionId ii } ii
  go other = other

-- | Returns the local variables that are in scope at a hole.
varsInScope :: InteractionId -> TCM [A.Name]
varsInScope ii = do
  m <- lookupInteractionId ii
  mi <- lookupMeta m
  let s = getMetaScope mi
      locals = map (localVar . snd) $ scopeLocals s
  return locals
