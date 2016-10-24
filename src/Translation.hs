module Translation where

import ProofSearch as P hiding (Var)

import Agda.Syntax.Common
import Agda.Syntax.Abstract as A
import Agda.Syntax.Translation.ConcreteToAbstract
import Agda.Syntax.Position
import Agda.Syntax.Abstract.Pretty
import Agda.Interaction.BasicOps as BO
import Agda.Interaction.CommandLine hiding (parseExpr)
import Agda.TypeChecking.Monad (TCM, lookupInteractionId)
import Control.Monad.State.Strict
import Data.List hiding (null)
import Data.Maybe
import Control.Applicative


import Prelude hiding (null)

import Control.Arrow ((***), first, second)
import Control.Applicative hiding (empty)
import Control.Monad.Reader
--import Control.Monad.State
import Control.Monad.Identity

import qualified Data.Map as Map
import Data.List hiding (null)
import Data.Maybe
import Data.Traversable hiding (mapM, forM, for)
import Data.Monoid

import qualified Agda.Syntax.Concrete as C -- ToDo: Remove with instance of ToConcrete
import Agda.Syntax.Position
import Agda.Syntax.Abstract.Views as A
import Agda.Syntax.Abstract.Pretty
import Agda.Syntax.Common
import Agda.Syntax.Info (ExprInfo(..),MetaInfo(..),emptyMetaInfo,exprNoRange)
import qualified Agda.Syntax.Info as Info
--import Agda.Syntax.Internal as I
import Agda.Syntax.Literal
import Agda.Syntax.Translation.InternalToAbstract
import Agda.Syntax.Translation.AbstractToConcrete
import Agda.Syntax.Translation.ConcreteToAbstract
import Agda.Syntax.Scope.Base
import Agda.Syntax.Scope.Monad
import Agda.Syntax.Fixity(Precedence(..))
import Agda.Syntax.Parser

import Agda.TheTypeChecker
import Agda.TypeChecking.Constraints
import Agda.TypeChecking.Conversion
import Agda.TypeChecking.Monad as M hiding (MetaInfo)
import Agda.TypeChecking.MetaVars
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Telescope
import Agda.TypeChecking.With
import Agda.TypeChecking.Coverage
import Agda.TypeChecking.Records
import Agda.TypeChecking.Irrelevance (wakeIrrelevantVars)
import Agda.TypeChecking.Pretty (prettyTCM)
import Agda.TypeChecking.Free
import Agda.TypeChecking.CheckInternal
import Agda.TypeChecking.SizedTypes.Solve
import qualified Agda.TypeChecking.Pretty as TP

import Agda.Utils.Except ( Error(strMsg), MonadError(catchError, throwError) )
import Agda.Utils.Functor
import Agda.Utils.Lens
import Agda.Utils.List
import Agda.Utils.Maybe
import Agda.Utils.Monad
import Agda.Utils.Null
import Agda.Utils.Pretty
import Agda.Utils.Permutation
import Agda.Utils.Size

import Prelude hiding (null)

generateGoal :: MonadIO m => Int -> [Declaration] -> StateT HintDB m [PsTerm]
generateGoal n decls = seqConcatM (map (genGoal n) decls)

genGoal :: MonadIO m => Int -> Declaration -> StateT HintDB m [PsTerm]
genGoal n (ScopedDecl _ decls)  = generateGoal n decls
genGoal n (A.Section _ _ _ decls) = generateGoal n decls
genGoal n (Mutual _ decls)      = generateGoal n decls
genGoal n (FunDef _ qn _ cls)    = seqConcatM $ map (\cl -> clauseToGoal cl (qNameS qn) n) cls
genGoal _ _ = return []

clauseToGoal :: MonadIO m => Clause -> String -> Int -> StateT HintDB m [PsTerm]
clauseToGoal (Clause _ (RHS e) _ _) fun n = do
    rule <- getRule fun
    liftIO $ putStrLn $ "expr: " ++ dprint e
    (prems,goals) <- exprToGoal e [ruleConclusion rule] n
    liftIO $ putStrLn $ "prems " ++ show prems
    return goals

exprToGoal :: MonadIO m => Expr -> [PsTerm] -> Int -> StateT HintDB m ([PsTerm], [PsTerm])
--exprToGoal e _ _ = liftIO (putStrLn (dprint e)) >> return ([],[])
exprToGoal (Def fun) ps n = do
    rule <- getRule (qNameS fun)
    return (rulePremises rule ++ ps, [])
exprToGoal (A.Con (AmbQ (c:_))) ps n = do
    rule <- getRule (qNameS c)
    return (rulePremises rule ++ ps, [])
exprToGoal (Lit l) (_:ps) n = return (ps, [])
exprToGoal (QuestionMark _ _) (ps:prems) n = return (prems, [ps])
exprToGoal (App _ e1 e2) ps n = do
    (prems, goals) <- exprToGoal e1 ps n    
    (prems', goals') <- exprToGoal (namedArg e2) prems n
    liftIO $ putStrLn $ "before: " ++ show ps
    liftIO $ putStrLn $ "After " ++ dprint e1 ++ ": " ++ show prems
    liftIO $ putStrLn $ "After " ++ dprint (namedArg e2) ++ ": " ++ show prems'
    return (prems', goals ++ goals')    

exprToGoal (ScopedExpr _ e) ps n = exprToGoal e ps n
exprToGoal e ps n = return (ps, [])

exprToGoal' :: MonadIO m => Expr -> [PsTerm] -> Int -> StateT HintDB m (Maybe PsTerm)
exprToGoal' f@(Fun _ (Arg _ (Var fun)) e) ps n = undefined 

makeRules :: MonadIO m => [Declaration] -> StateT HintDB m HintDB
makeRules decls = mapStateM makeRules' decls >> get

makeRules' :: MonadIO m => Declaration -> StateT HintDB m ()
makeRules' (ScopedDecl _ decls) = mapStateM makeRules' decls
makeRules' (A.Section _ _ _ decls) = mapStateM makeRules' decls
makeRules' (Mutual _ decls) = mapStateM makeRules' decls
makeRules' d = makeRule d

makeRule :: MonadIO m => Declaration -> StateT HintDB m ()
makeRule (DataSig _ n _ e) = return ()
makeRule (DataDef _ _ _ cons) = dataDefToRule cons
makeRule (A.Axiom _ _ _ n e) =  maybe (return ()) (addRule . mkRule (qNameS n)) (exprToCon e)
makeRule (FunDef _ n _ cls) = mapM_ clauseToRule cls
makeRule (Pragma _ _) = return ()

dataDefToRule :: MonadIO m => [Constructor] -> StateT HintDB m ()
dataDefToRule [] = return ()
dataDefToRule (A.Axiom _ _ _ qn e:xs) = do
    dataDefToRule xs
    maybe (return ()) (addRule . mkRule (qNameS qn)) (exprToCon e)

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
    addRule r
patternToRule (ConP _ n xs) ps = do
    prems <- getPremises (qNameS (head $ unAmbQ n))
    patternsToRules (map (namedThing . unArg) xs) prems

splitPsTerm :: PsTerm -> (PsTerm, [PsTerm])
splitPsTerm (P.Con "->" terms) = (last terms, init terms)
splitPsTerm ps = (ps,[])

getPremises :: MonadIO m => String -> StateT HintDB m [PsTerm]
getPremises s = do
    rule <- getRule s
    return $ rulePremises rule

-- Expressions to PsTerms

exprToCon :: Expr -> Maybe (PsTerm, [PsTerm])
exprToCon (ScopedExpr _ e) = exprToCon e
exprToCon (Pi _ _ e) = exprToCon e
exprToCon (Def qn) = Just $ (var $ qNameS qn,[])
exprToCon (Fun _ arg e) = exprToCon e >>= \(concl, prems) -> Just $ (concl, exprToConPrem (unArg arg) ++ prems)
exprToCon (Set _ _) = Nothing
exprToCon e = error $ show e

exprToConPrem :: Expr -> [PsTerm]
exprToConPrem (ScopedExpr _ e) = exprToConPrem e
exprToConPrem (Def qn) = [var $ qNameS qn]

-- Turn names into strings

qNameS :: QName -> String
qNameS (QName m n) = show $ nameConcrete n

nameS :: Name -> String
nameS = show . nameConcrete



---------------------------------------------
-- Proof to Abstract syntax

proofToAbstract :: Proof -> HintDB -> Int -> TCM Expr
proofToAbstract (Proof ruleIdent _) hdb n = do
    let rule = find (\x -> ruleName x == ruleIdent) hdb
    e <- parseExpr noRange "zero"
    abstr <- toAbstract e
    --abstr' <- evalInCurrent abstr
    liftIO $ putStrLn $ show abstr
    e' <- Translation.refine (InteractionId 0) Nothing abstr
    --e <- lookupInteractionId (InteractionId 0)
    liftIO $ putStrLn $ show e'
    --liftIO $ putStrLn $ "test : " ++ show e
    --a <- metaParseExpr (InteractionId 0) "zero"
    --liftIO $ putStrLn $ show a
    --actOnMeta ["0","Example2.Nat.zero"] (\ii -> \e -> refine ii Nothing e)
    error "test"
    --return abstr
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

seqConcatM :: MonadIO m =>  [StateT HintDB m [a]] -> StateT HintDB m [a]
seqConcatM = fmap concat . sequence

class DebugPrint a where
    dprint :: a -> String

instance DebugPrint Expr where
    dprint (Var n) = "(Var " ++ nameS n ++ ")"
    dprint (Def qn) = "(Def " ++ qNameS qn ++ ")"
    dprint (A.Con (AmbQ qns)) = "(Con " ++ show (map qNameS qns) ++ ")"
    dprint (Lit l) = "(Lit " ++ show l ++ ")"
    dprint (QuestionMark _ ident) = show ident
    dprint (App _ e narg) = "(App " ++ dprint e ++ " " ++ dprint (namedArg narg) ++ ")"
    dprint (ScopedExpr _ e) = dprint e--"(ScopedExpr " ++ dprint e ++ ")"

refine
  :: InteractionId  -- ^ Hole.
  -> Maybe Range
  -> Expr           -- ^ The expression to refine the hole with.
  -> TCM Expr       -- ^ The successfully given expression.
refine ii mr e = do
  mi <- lookupInteractionId ii
  mv <- lookupMeta mi
  let range = fromMaybe (getRange mv) mr
      scope = M.getMetaScope mv
  reportSDoc "interaction.refine" 10 $
    TP.text "refining with expression" TP.<+> prettyTCM e
  reportSDoc "interaction.refine" 50 $
    TP.text $ show $ deepUnscope e
  -- We try to append up to 10 meta variables
  tryRefine 10 range scope e
  where
    tryRefine :: Int -> Range -> ScopeInfo -> Expr -> TCM Expr
    tryRefine nrOfMetas r scope e = try nrOfMetas e
      where
        try :: Int -> Expr -> TCM Expr
        try 0 e = throwError $ strMsg "Cannot refine"
        try n e = give ii (Just r) e `catchError` (\_ -> try (n - 1) =<< appMeta e)

        -- Apply A.Expr to a new meta
        appMeta :: Expr -> TCM Expr
        appMeta e = do
          let rng = rightMargin r -- Andreas, 2013-05-01 conflate range to its right margin to ensure that appended metas are last in numbering.  This fixes issue 841.
          -- Make new interaction point
          ii <- registerInteractionPoint rng Nothing
          let info = Info.MetaInfo
                { Info.metaRange = rng
                , Info.metaScope = scope { scopePrecedence = ArgumentCtx }
                , metaNumber = Nothing -- in order to print just as ?, not ?n
                , metaNameSuggestion = ""
                }
              metaVar = QuestionMark info ii

              count x e = getSum $ foldExpr isX e
                where isX (A.Var y) | x == y = Sum 1
                      isX _                  = mempty

              lamView (A.Lam _ (DomainFree _ x) e) = Just (x, e)
              lamView (A.Lam i (DomainFull (TypedBindings r (Arg ai (TBind br (x : xs) a)))) e)
                | null xs   = Just (dget x, e)
                | otherwise = Just (dget x, A.Lam i (DomainFull $ TypedBindings r $ Arg ai $ TBind br xs a) e)
              lamView _ = Nothing

              -- reduce beta-redexes where the argument is used at most once
              smartApp i e arg =
                case lamView $ unScope e of
                  Just (x, e) | count x e < 2 -> mapExpr subX e
                    where subX (A.Var y) | x == y = namedArg arg
                          subX e = e
                  _ -> App i e arg

          liftIO $ putStrLn $ show $ e
          return $ smartApp (ExprRange r) e $ defaultNamedArg metaVar
          --ToDo: The position of metaVar is not correct
          --ToDo: The fixity of metavars is not correct -- fixed? MT