{-| This module contains the functionality to translate Agda terms to proof search terms.
-}
module Translation
  ( goalAndRules
  , generateHints
  , generateGoal
  ) where

import qualified Agda.Interaction.BasicOps                  as B
import qualified Agda.Syntax.Abstract                       as A
import           Agda.Syntax.Common
import           Agda.Syntax.Info
import qualified Agda.Syntax.Internal                       as I
import           Agda.Syntax.Translation.InternalToAbstract
import           Agda.TypeChecking.Monad
import           Agda.TypeChecking.Monad.Builtin
import           Agda.Utils.Except
import           Agda.Utils.Pretty

import           Control.Arrow
import           Control.Monad
import           Control.Monad.Trans.Maybe

import qualified AgdaUtil                                   as AU
import           Debug.Trace
import qualified ProofSearch                                as Ps

-- | For an interaction point, returns the proof search term representing the goal
-- and a hint database containing all definitions that are in scope.
goalAndRules :: InteractionId -> TCM (Ps.PsTerm, Ps.HintDB)
goalAndRules ii = do
  -- returns the type of the interaction point (safe to pattern match, result is always "B.OfType")
  B.OfType _ ty <- B.typeOfMeta B.Normalised ii
  (,)
    <$> (runMaybeT (generateGoal ty) >>= maybe (throwError $ strMsg "invalid goal") pure)
    <*> generateHints ii

-- | Generates a hint database from a list of definitions,
-- consisting of either a local or a global name together with a type.
generateHints :: InteractionId -> TCM Ps.HintDB
generateHints ii = AU.thingsInScopeWithType ii >>= \sigs -> concat <$> mapM build sigs where
  -- makes a string with an unqualified name
  nameStr = either prettyShow qNameS
  build (def, ty) = generateRules (nameStr def) ty

-- | Generates rules for an identifier with the given name and type.
-- For things of function types, it returns a rule where the return value is
-- the conclusion and the arguments are premises. Additionally, it returns
-- a rule with just a conclusion using the @->@ constructor to represent functions.
-- Hints of that form allows directly passing un-applied functions as arguments.
generateRules :: String -> A.Expr -> TCM [Ps.Rule]
generateRules name expr = mkRules <$> runMaybeT (typeToPsTerms convertVarForRule [] expr) where
  mkRules Nothing = [] -- rule generation failed here
  mkRules (Just []) = []
  mkRules (Just terms) = uncurry (Ps.Rule name) (split terms) :
      [Ps.Rule name (mkFunType terms) [] | length terms > 1]

  split []     = error "IMPOSSIBLE"
  split [x]    = (x, [])
  split (x:xs) = second (x:) $ split xs

-- | Generates a proof search term from the goal type.
generateGoal :: A.Expr -> MaybeT TCM Ps.PsTerm
generateGoal = typeToPsTermFun convertVarForGoal []

-- | This takes an expression and flattens all top level binary application constructors into a list.
-- For example, it will turn @(f x) y@ into @[f, x, y]@.
-- If there is no application, a singleton list is returned, i.e. a single @x@ is transformed into @[x]@.
-- Implicit arguments are left out.
flattenVisibleApp :: A.Expr -> [A.Expr]
flattenVisibleApp (A.App _ f x) = flattenVisibleApp f ++ [ namedThing $ unArg x | not (isHiddenArg x) ]
flattenVisibleApp (A.ScopedExpr _ e) = flattenVisibleApp e
flattenVisibleApp other = [other]

-- | Extracts all bindings from a Pi-type telescope together with their visibility.
telescopeBindings :: A.Telescope -> [(A.Name, Hiding, A.Expr)]
telescopeBindings = concatMap go where
  go (A.TypedBindings _ arg) = case unArg arg of
    A.TBind _ names ty -> concatMap (mk (argInfoHiding $ argInfo arg) ty) names
    A.TLet _ _ -> [] -- somehow used for let bindings, not relevant for us

  mk h ty (WithHiding h2 n) = [(n, mappend h h2, ty)]

-- | Checks whether an argument is implicit.
isHiddenArg :: Arg a -> Bool
isHiddenArg arg = argInfoHiding (argInfo arg) == Hidden

-- | Variable conversion function taking a scope and a name, turning it into a PsTerm.
type ConvertVar = [A.Name] -> A.Name -> Ps.PsTerm

-- | Variable conversion function when generating rules.
-- In this case, variables that are mentioned in the scope have been introduced
-- through Pi-types. This means, they should be variables in the proof search.
-- Variables that are not mentioned in the scope have been declared before, such as it
-- is the case with variables occurring in the types of local variables.
-- These are converted into constants to block unification
-- (they appear to have an unspecified, but concrete type).
convertVarForRule :: ConvertVar
convertVarForRule scope name
  | name `elem` scope = Ps.var (prettyShow name)
  | otherwise = Ps.con (prettyShow name)

-- | Variable conversion function when generating the goal term.
-- In the goal, all variables are converted to constants since no new variables are
-- introduced at that point.
convertVarForGoal :: ConvertVar
convertVarForGoal _ = Ps.con . prettyShow

-- | Takes a type and converts it to a list of PsTerms corresponding to function arguments and return value.
-- That means, a function type @A -> B -> C@ is converted to a list @[term(A), term(B), term(C)]@.
typeToPsTerms :: ConvertVar -- ^ a function to convert variables
              -> [A.Name] -- ^ the list of names that have been introduced in this type so far
              -> A.Expr -- ^ the type being converted
              -> MaybeT TCM [Ps.PsTerm]
-- ignore scoped expressions since we keep track of the scope ourselves here
typeToPsTerms cv scope (A.ScopedExpr _ e) = typeToPsTerms cv scope e
-- non-dependent function ...
typeToPsTerms cv scope (A.Fun _ arg ret)
  -- ... with an implicit argument
  | isHiddenArg arg = typeToPsTerms cv scope ret
  -- ... with an explicit argument that needs to be converted as well
  | otherwise = do
      argTerm <- typeToPsTermFun cv scope (unArg arg)
      (argTerm :) <$> typeToPsTerms cv scope ret
-- a dependent function arrow (pi-type)
typeToPsTerms cv scope (A.Pi _ tel ret) = piTypeToPsTerms cv scope (telescopeBindings tel) ret
-- any other syntactic elements are flattened to a list of applications
typeToPsTerms cv scope other = case flattenVisibleApp other of
  [] -> mzero -- should not happen
  (A.Var var : args)
    | null args -> return [cv scope var] -- allowed
    | otherwise -> mzero -- higher kinded type variables are not supported
  -- definitions and constructors are always translated to constants with the appropriate arguments
  (A.Def def : args) -> fromDefOrCon cv scope (qNameS def) args
  (A.Con con : args) -> fromDefOrCon cv scope (qNameS $ head $ A.unAmbQ con) args
  -- translate literal naturals
  (A.Lit lit : _) -> do
    con <- MaybeT $ fmap Just (constructorForm (I.Lit lit) >>= reify) `catchError` \_ -> return Nothing
    typeToPsTerms cv scope con
  -- set expressions
  (A.Set _ lvl : _) -> return [Ps.con "Set" (Ps.con $ show lvl)]
  -- fresh metas somewhere in the type can be turned into variables
  (A.Underscore mi : _) -> do
    let uname = "_" ++ metaNameSuggestion mi ++ "_" ++ maybe "" show (metaNumber mi)
    return [Ps.var uname]
  -- unsupported syntax
  what -> traceM ("UNSUPPORTED " ++ show what) >> mzero -- unsupported syntax

-- | Combines a list of terms with function arrows.
mkFunType :: [Ps.PsTerm] -> Ps.PsTerm
mkFunType = foldr1 (Ps.con "->")

-- | Creates a PsTerm representing a function type.
typeToPsTermFun :: ConvertVar -> [A.Name] -> A.Expr -> MaybeT TCM Ps.PsTerm
typeToPsTermFun cv scope e = mkFunType <$> typeToPsTerms cv scope e

-- | Creates a PsTerm for a A.Def or A.Con.
fromDefOrCon :: ConvertVar -> [A.Name] -> String -> [A.Expr] -> MaybeT TCM [Ps.PsTerm]
fromDefOrCon cv scope def args = (return . Ps.Con def) <$> mapM (typeToPsTermFun cv scope) args

-- | Converts a pi type to the corresponding PsTerms.
piTypeToPsTerms :: ConvertVar -> [A.Name] -> [(A.Name, Hiding, A.Expr)] -> A.Expr -> MaybeT TCM [Ps.PsTerm]
piTypeToPsTerms cv scope [] ret = typeToPsTerms cv scope ret
piTypeToPsTerms cv scope ((argName, h, argTy):args) ret = case h of
  Hidden -> piTypeToPsTerms cv (argName : scope) args ret
  _ -> (:)
    <$> typeToPsTermFun cv scope argTy
    <*> piTypeToPsTerms cv (argName : scope) args ret

-- | Returns the actual identifier from a qualified name.
qNameS :: A.QName -> String
qNameS (A.QName _ n) = show $ A.nameConcrete n

