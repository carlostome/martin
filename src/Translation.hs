module Translation
(
    goalAndRules,
    makeRules,
    generateGoal
) where

import ProofSearch as P

import Control.Monad.State.Strict
import Control.Applicative
import Data.Foldable                                (fold, foldMap)
import Data.Monoid                                  ((<>))
import Data.List hiding                             (null)
import Data.Maybe

import Agda.Syntax.Common
import Agda.Syntax.Abstract as A
import Agda.Syntax.Translation.ConcreteToAbstract
import Agda.Syntax.Position
import Agda.Syntax.Abstract.Pretty
import Agda.Interaction.BasicOps as BO
import Agda.Interaction.CommandLine hiding          (parseExpr)
import Agda.TypeChecking.Monad                      (TCM, lookupInteractionId)



import Debug.Trace 

-- Top level functions

-- Use these to create all the rules and generate a goal

goalAndRules :: [Declaration] -> InteractionId -> TCM (PsTerm, HintDB)
goalAndRules decls (InteractionId i) = runStateT ( do
    makeRules decls i
    --printRules -- Uncomment to print out generated rules
    goal <- generateGoal decls i
    return (fromJust goal) )[]

makeRules :: MonadIO m => [Declaration] -> Int -> StateT HintDB m HintDB
makeRules decls n = mapStateM (flip makeRules' n) decls >> delLevelRules >> get


generateGoal :: MonadIO m => [Declaration] -> Int -> StateT HintDB m (Maybe PsTerm)
generateGoal decls n = maybeConcatM (map (flip genGoal n) decls)


-- Goal generation

genGoal :: MonadIO m => Declaration -> Int -> StateT HintDB m (Maybe PsTerm)
genGoal (ScopedDecl _ decls)    n = generateGoal decls n
genGoal (A.Section _ _ _ decls) n = generateGoal decls n
genGoal (Mutual _ decls)        n = generateGoal decls n
genGoal (FunDef _ qn _ cls)     n = maybeConcatM $ map (\cl -> clauseToGoal cl (qNameS qn) n) cls
genGoal _ _ = return Nothing

clauseToGoal :: MonadIO m => Clause -> String -> Int -> StateT HintDB m (Maybe PsTerm)
clauseToGoal (Clause (LHS _ core pats) (RHS e) _ _) fun n = do
    let mg = containsGoal e n
    rule <- getRule fun
    (prems,goals) <- exprToGoal e [ruleConclusion rule] n
    return goals


exprToGoal :: MonadIO m => Expr -> [PsTerm] -> Int -> StateT HintDB m ([PsTerm], Maybe PsTerm)
exprToGoal (Def fun) ps n = do
    rule <- getRule (qNameS fun)
    return (rulePremises rule ++ ps, Nothing)
exprToGoal (A.Con (AmbQ (c:_))) ps n = do
    rule <- getRule (qNameS c)
    return (rulePremises rule ++ ps, Nothing)
exprToGoal (Lit l) (_:ps) n = return (ps, Nothing)
exprToGoal (QuestionMark _ _) (ps:prems) n = return (prems, Just $ varToCon ps)
exprToGoal (App _ e1 e2) ps n = do
    (prems, goals) <- exprToGoal e1 ps n
    (prems', goals') <- exprToGoal (namedArg e2) prems n
    return (prems', goals <|> goals')    
exprToGoal (ScopedExpr _ e) ps n = exprToGoal e ps n
exprToGoal e ps n = return (ps, Nothing)

------------------------------------------------------
-- Build the HintDB by generating rules

-- Remove the rules defined by level
delLevelRules :: MonadIO m => StateT HintDB m ()
delLevelRules = modify (filter (\r -> ruleName r /= "lzero" &&
                                      ruleName r /= "lsuc"  &&
                                      ruleName r /= "_\8852_"))

-- Make rules for a given declaration
makeRules' :: MonadIO m => Declaration -> Int -> StateT HintDB m ()
makeRules' (ScopedDecl _ decls)    n = mapStateM (flip makeRules' n) decls
makeRules' (A.Section _ _ _ decls) n = mapStateM (flip makeRules' n) decls
makeRules' (Mutual _ decls)        n = mapStateM (flip makeRules' n) decls
makeRules' (DataSig _ n _ e)       _ = return () -- Ẃe don't have to generate a rule for this
makeRules' (DataDef _ _ _ cons)    i = dataDefToRule cons
makeRules' (A.Axiom _ _ _ n e)     i = maybe (return ()) (addRule . mkRule (qNameS n)) (exprToPsTerm e)
makeRules' (FunDef _ n _ cls)      i = mapM_ (flip clauseToRule i) cls
makeRules' (Pragma _ _)            _ = return () -- same

dataDefToRule :: MonadIO m => [Constructor] -> StateT HintDB m ()
dataDefToRule [] = return ()
dataDefToRule (A.Axiom _ _ _ qn e:xs) = do
    dataDefToRule xs
    maybe (return ()) (addRule . mkRule (qNameS qn)) (exprToPsTerm e)

clauseToRule :: MonadIO m => Clause -> Int -> StateT HintDB m ()
clauseToRule (Clause (LHS _ core pats) (RHS e) _ _) n = when (isJust $ containsGoal e n) $ lhsCoreToRules core

lhsCoreToRules :: MonadIO m => LHSCore -> StateT HintDB m ()
lhsCoreToRules (LHSHead n xs) = do
    prems <- getPremises (qNameS n)
    patternsToRules (map (namedThing . unArg) xs) prems


----------------------------------------
-- Patterns

patternsToRules :: MonadIO m => [Pattern] -> [PsTerm] -> StateT HintDB m ()
patternsToRules ptrns psterms = mapM_ (\(x,y) -> patternToRule x y) $ zip ptrns psterms

patternToRule :: MonadIO m => Pattern -> PsTerm  -> StateT HintDB m ()
patternToRule (VarP n) ps = do
    let r = (\(concl,prems) -> Rule (nameS n) concl prems) (splitPsTerm ps)
    addRule r
patternToRule (ConP _ n xs) ps = do
    prems <- getPremises (qNameS (head $ unAmbQ n))
    patternsToRules (map (namedThing . unArg) xs) prems

splitPsTerm :: PsTerm -> (PsTerm, [PsTerm])
splitPsTerm (P.Con "->" terms) = (last terms, init terms)
splitPsTerm ps = (varToCon ps,[])

getPremises :: MonadIO m => String -> StateT HintDB m [PsTerm]
getPremises s = do
    rule <- getRule s
    return $ rulePremises rule

-- Expressions to PsTerms

exprToPsTerm :: Expr -> Maybe (PsTerm, [PsTerm])
exprToPsTerm (ScopedExpr _ e) = exprToPsTerm e
exprToPsTerm (Pi _ _ e) = exprToPsTerm e
exprToPsTerm (Def qn) = Just $ (con $ qNameS qn,[])
exprToPsTerm (Fun _ arg e) = exprToPsTerm e >>= \(concl, prems) -> Just $ (concl, exprToPsTermPrem (unArg arg) ++ prems)
exprToPsTerm (Set _ _) = Nothing
exprToPsTerm (App _ _ _) = Nothing

exprToPsTermPrem :: Expr -> [PsTerm]
exprToPsTermPrem (ScopedExpr _ e) = exprToPsTermPrem e
exprToPsTermPrem (Def qn) = [var $ qNameS qn]

containsGoal :: Expr -> Int -> Maybe InteractionId
containsGoal (ScopedExpr _ e) n = containsGoal e n
containsGoal (Fun _ arg e) n = containsGoal (unArg arg) n <|> containsGoal e n
containsGoal (QuestionMark _ ii@(InteractionId i)) n
    | i == n = Just ii
    | otherwise = Nothing
containsGoal _ _ = Nothing

-- Turn names into strings

qNameS :: QName -> String
qNameS (QName m n) = show $ nameConcrete n

nameS :: Name -> String
nameS = show . nameConcrete

---------------------------------------------
-- Some Helper functions

mkRule :: String -> (PsTerm, [PsTerm]) -> Rule
mkRule n (concl, prems) = Rule n concl prems 

getRule :: Monad m => String -> StateT HintDB m Rule
getRule s = do
    hdb <- get
    let (Just rule) = find (\a -> ruleName a == s) hdb
    return rule

addRule :: MonadIO m => Rule -> StateT HintDB m ()
addRule rule = modify ((:) rule)

mapStateM :: MonadIO m => (a -> StateT HintDB m ()) -> [a] -> StateT HintDB m ()
mapStateM f xs = mapM_ f xs 

maybeConcatM :: MonadIO m => [StateT HintDB m (Maybe a)] -> StateT HintDB m (Maybe a)
maybeConcatM = fmap (foldr (\x acc -> x <|> acc) Nothing) . sequence

varToCon :: PsTerm -> PsTerm
varToCon (P.Var (P.Raw n)) = P.Con n []
varToCon (P.Con n xs) = P.Con n (map varToCon xs)

class DebugPrint a where
    dprint :: a -> String

instance DebugPrint Expr where
    dprint (A.Var n) = "(Var " ++ nameS n ++ ")"
    dprint (Def qn) = "(Def " ++ qNameS qn ++ ")"
    dprint (A.Con (AmbQ qns)) = "(Con " ++ show (map qNameS qns) ++ ")"
    dprint (Lit l) = "(Lit " ++ show l ++ ")"
    dprint (QuestionMark _ ident) = show ident
    dprint (App _ e narg) = "(App " ++ dprint e ++ " " ++ dprint (namedArg narg) ++ ")"
    dprint (ScopedExpr _ e) = dprint e--"(ScopedExpr " ++ dprint e ++ ")"


printRules :: MonadIO m => StateT HintDB m ()
printRules = do
    hdb <- get
    mapM_ (\x -> liftIO $ putStrLn $ show x ++ "\n") hdb
