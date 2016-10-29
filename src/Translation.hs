module Translation where

import qualified Agda.Interaction.BasicOps as B
import qualified Agda.Syntax.Abstract      as A
import           Agda.Syntax.Common
import           Agda.Syntax.Literal
import           Agda.Syntax.Scope.Base
import           Agda.TypeChecking.Monad
import           Agda.Utils.Except
import           Agda.Utils.Pretty

import           Control.Arrow
import qualified Data.Set                  as Set

import           Debug.Trace
import qualified ProofSearch               as Ps

goalAndRules :: InteractionId -> TCM (Ps.PsTerm, Ps.HintDB)
goalAndRules ii = do
  scope <- thingsInScopeWithType ii
  B.OfType _ ty <- B.typeOfMeta B.Normalised ii
  (,)
    <$> maybe (throwError $ strMsg "invalid goal") pure (generateGoal ty)
    <*> pure (generateHints scope)

generateHints :: [(Either A.Name A.QName, A.Expr)] -> Ps.HintDB
generateHints = concatMap build where
  nameStr = either prettyShow qNameS
  build (def, ty) = generateRules (nameStr def) ty

generateRules :: String -> A.Expr -> [Ps.Rule]
generateRules name expr =
  case typeToPsTerms convertVarForRule [] expr of
    Nothing -> [] -- rule generation failed here
    Just [] -> []
    Just terms -> uncurry (Ps.Rule name) (split terms) :
      [Ps.Rule name (mkFunType terms) [] | length terms > 1]
  where
    split []     = error "IMPOSSIBLE"
    split [x]    = (x, [])
    split (x:xs) = second (x:) $ split xs

generateGoal :: A.Expr -> Maybe Ps.PsTerm
generateGoal = typeToPsTermFun convertVarForGoal []

-- | This takes an expression and flattens all top level binary application constructors into a list.
-- For example, it will turn @(f x) y@ into @[f, x, y]@.
-- If there is no application, a singleton list is returned, i.e. a single @x@ is transformed into @[x]@.
flattenVisibleApp :: A.Expr -> [A.Expr]
flattenVisibleApp (A.App _ f x)
  | isHiddenArg x = flattenVisibleApp f
  | otherwise = flattenVisibleApp f ++ [namedThing $ unArg x]
flattenVisibleApp (A.ScopedExpr _ e) = flattenVisibleApp e
flattenVisibleApp other = [other]

-- | Extracts all visible (i.e. non-implicit) bindings from a Pi-type telescope.
telescopeBindings :: A.Telescope -> [(A.Name, Hiding, A.Expr)]
telescopeBindings = concatMap go where
  go (A.TypedBindings _ arg) = case unArg arg of
    A.TBind _ names ty -> concatMap (mk (argInfoHiding $ argInfo arg) ty) names
    A.TLet _ _ -> [] -- somehow used for let bindings, not relevant for us

  mk h ty (WithHiding h2 n) = [(n, mappend h h2, ty)]

isHiddenArg :: Arg a -> Bool
isHiddenArg arg = argInfoHiding (argInfo arg) == Hidden

type ConvertVar = [A.Name] -> A.Name -> Ps.PsTerm

convertVarForRule :: ConvertVar
convertVarForRule scope name
  | name `elem` scope = Ps.var (prettyShow name)
  | otherwise = Ps.con (prettyShow name)

convertVarForGoal :: ConvertVar
convertVarForGoal _ = Ps.con . prettyShow

typeToPsTerms :: ConvertVar -> [A.Name] -> A.Expr -> Maybe [Ps.PsTerm]
typeToPsTerms cv scope (A.ScopedExpr _ e) = typeToPsTerms cv scope e
typeToPsTerms cv scope (A.Fun _ arg ret)
  | isHiddenArg arg = typeToPsTerms cv scope ret
  | otherwise = do
      argTerm <- typeToPsTermFun cv scope (unArg arg)
      (argTerm :) <$> typeToPsTerms cv scope ret
typeToPsTerms cv scope (A.Pi _ tel ret) = piTypeToPsTerms cv scope (telescopeBindings tel) ret
typeToPsTerms cv scope other = case flattenVisibleApp other of
  [] -> Nothing -- should not happen
  (A.Var var : args)
    | null args -> Just [cv scope var] -- allowed
    | otherwise -> Nothing -- higher kinded type variables are not supported
  (A.Def def : args) -> fromDefOrCon cv scope (qNameS def) args
  (A.Con con : args) -> fromDefOrCon cv scope (qNameS $ head $ A.unAmbQ con) args
  (A.Lit (LitNat _ i) : _) -> Just [natToTerm i]
  (A.Set _ lvl : _) -> Just [Ps.con "Set" (Ps.con $ show lvl)]
  what -> trace ("UNSUPPORTED " ++ show what) Nothing -- unsupported syntax

natToTerm :: Integer -> Ps.PsTerm
natToTerm n
  | n < 0 = error "negative natural number"
  | n == 0 = Ps.con "zero"
  | otherwise = Ps.con "suc" $ natToTerm (n - 1)

mkFunType :: [Ps.PsTerm] -> Ps.PsTerm
mkFunType = foldr1 (Ps.con "->")

-- | Creates a PsTerm representing a function type.
typeToPsTermFun :: ConvertVar -> [A.Name] -> A.Expr -> Maybe Ps.PsTerm
typeToPsTermFun cv scope e = mkFunType <$> typeToPsTerms cv scope e

-- | Creates a PsTerm for a A.Def or A.Con.
fromDefOrCon :: ConvertVar -> [A.Name] -> String -> [A.Expr] -> Maybe [Ps.PsTerm]
fromDefOrCon cv scope def args = (return . Ps.Con def) <$> mapM (typeToPsTermFun cv scope) args

-- | Converts a pi type to the corresponding PsTerms.
piTypeToPsTerms :: ConvertVar -> [A.Name] -> [(A.Name, Hiding, A.Expr)] -> A.Expr -> Maybe [Ps.PsTerm]
piTypeToPsTerms cv scope [] ret = typeToPsTerms cv scope ret
piTypeToPsTerms cv scope ((argName, h, argTy):args) ret = case h of
  Hidden -> piTypeToPsTerms cv (argName : scope) args ret
  _ -> maybe id (:) (typeToPsTermFun cv scope argTy)
    <$> piTypeToPsTerms cv (argName : scope) args ret

qNameS :: A.QName -> String
qNameS (A.QName _ n) = show $ A.nameConcrete n

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
