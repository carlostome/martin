module Translation where

import ProofSearch

import Agda.Syntax.Common
import Agda.Syntax.Abstract hiding (Con)
import Agda.Syntax.Abstract.Pretty
import Control.Monad.State.Strict
import Data.List


-- TODO: Generate rules in local scope
-- TODO: Convert goal to PsTerm
makeRules :: MonadIO m => [Declaration] -> StateT HintDB m HintDB
makeRules decls = mapStateM makeRules' decls >> get

makeRules' :: MonadIO m => Declaration -> StateT HintDB m ()
makeRules' (ScopedDecl _ decls) = mapStateM makeRules' decls
makeRules' (Section _ _ _ decls) = mapStateM makeRules' decls
makeRules' (Mutual _ decls) = mapStateM makeRules' decls
makeRules' d = makeRule d

makeRule :: MonadIO m => Declaration -> StateT HintDB m ()
makeRule (DataSig _ n _ e) = return ()
makeRule (DataDef _ _ _ cons) = dataDefToRule cons
makeRule (Axiom _ _ _ n e) = do
    let r = (\(concl, prems) -> Rule (qNameS n) concl prems) (exprToCon e) 
    addRules [r]
makeRule (FunDef _ n _ cls) = mapM_ clauseToRule cls

dataDefToRule :: MonadIO m => [Constructor] -> StateT HintDB m ()
dataDefToRule [] = return ()
dataDefToRule (Axiom _ _ _ qn e:xs) = do
    let r = (Rule (qNameS qn) (fst $ exprToCon e) (snd $ exprToCon e)) 
    dataDefToRule xs
    addRules [r]    

clauseToRule :: MonadIO m => Clause -> StateT HintDB m ()
clauseToRule (Clause (LHS _ core pats) rhs _ _) = lhsCoreToRules core

lhsCoreToRules :: MonadIO m => LHSCore -> StateT HintDB m ()
lhsCoreToRules (LHSHead n xs) = do
    prems <- getPremises (qNameS n)
    patternsToRules (map (namedThing . unArg) xs) prems


----------------------------------------
-- Patterns

patternsToRules :: MonadIO m => [Pattern] -> [PsTerm] -> StateT HintDB m ()
patternsToRules [] [] = return ()
patternsToRules (ptrn:ptrns) (pst:psterms) = do
    patternToRule ptrn pst
    patternsToRules ptrns psterms

patternToRule :: MonadIO m => Pattern -> PsTerm -> StateT HintDB m ()
patternToRule (VarP n) ps = do
    let r = (\(concl,prems) -> Rule (nameS n) concl prems) (splitPsTerm ps)
    addRules [r]
patternToRule (ConP _ n xs) ps = do
    prems <- getPremises (qNameS (head $ unAmbQ n))
    patternsToRules (map (namedThing . unArg) xs) prems

splitPsTerm :: PsTerm -> (PsTerm, [PsTerm])
splitPsTerm (Con "->" terms) = (last terms, init terms)
splitPsTerm ps = (ps,[])

getPremises :: MonadIO m => String -> StateT HintDB m [PsTerm]
getPremises s = do
    hdb <- get
    let (Just rule) = find (\a -> ruleName a == s) hdb
    return $ rulePremises rule

-- Expressions to PsTerms

exprToCon :: Expr -> (PsTerm, [PsTerm])
exprToCon (ScopedExpr _ e) = exprToCon e
exprToCon (Def qn) = (var $ qNameS qn,[])
exprToCon (Fun _ arg e) = (fst $ exprToCon e, exprToConPrem (unArg arg) ++ snd (exprToCon e))

exprToConPrem :: Expr -> [PsTerm]
exprToConPrem (ScopedExpr _ e) = exprToConPrem e
exprToConPrem (Def qn) = [var $ qNameS qn]

-- Turn names into strings

qNameS :: QName -> String
qNameS (QName m n) = show $ nameConcrete n

nameS :: Name -> String
nameS = show . nameConcrete



---------------------------------------------
-- Some combinators

addRules :: MonadIO m => HintDB -> StateT HintDB m ()
addRules hdb = modify ((++) hdb)

mapStateM :: MonadIO m => (a -> StateT HintDB m ()) -> [a] -> StateT HintDB m ()
mapStateM f xs = mapM_ f xs 