{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}

module Lib
    ( someFunc
    ) where

import qualified Agda.Syntax.Abstract as A
import Agda.Syntax.Translation.ConcreteToAbstract
import Agda.Syntax.Concrete
import Agda.Syntax.Common
import Agda.Main
import Agda.Syntax.Parser
import Agda.Syntax.Literal
import Agda.Syntax.Fixity
import Agda.Utils.FileName
import Control.Monad.IO.Class

-- Two ways of parsing agda programs
-- Either we parse a full agda program from a file
-- or we parse a given expression

-- The Agda library contains a pretty printer, which can be
-- called with show
someFunc :: IO ()
someFunc = do
    -- Parse an agda file and debugprint it
    -- Requires the path to be absolute
    let path = "/home/ferdinand/University/TFL/martin/examples/Example2.agda"
    s <- parseFile' moduleParser (mkAbsolute path)
    runTCMPrettyErrors $ test s
    --putStrLn $ dprint s
    --putStrLn $ show s

    -- Parse an expression and debugprint it
    -- s <- getLine
    -- putStrLn $ dprint $ parse exprParser s

    -- Pretty print any agda syntax
    -- putStrLn $ show s
    return ()

test concrt = do
    abstr <- toAbstract concrt
    liftIO $ putStrLn $ show abstr


-- For now the idea is to write an instance for each datatype that we 
-- actually use. For anything that we do not use, we should write an error
-- so that we know it doesn have a correct debugprinter.
-- Code isn't exactly the prettiest, we might want to rewrite it a bit later on

-- Note that debugprinting is unfinished
dprints :: DebugPrint a => [a] -> String
dprints xs = "[" ++ foldr (\x acc -> dprint x ++ ", " ++ acc) "]" xs

class DebugPrint a where
    dprint :: a -> String

instance DebugPrint ([Pragma],[Declaration]) where
    dprint (_, decls) = foldr (\x acc -> dprint x ++ "\n" ++ acc) "" decls

instance DebugPrint Declaration where
    dprint (TypeSig argInfo n e) = "TypeSig " ++ show argInfo ++ " " ++ dprint n ++ " " ++ dprint e ++ ""
    dprint (Field _ _ _) = "Field"
    dprint (FunClause lhs rhs whereCl b) = "FunClause " ++ dprint lhs ++ " " ++ dprint rhs
                                            ++ " " ++ dprint whereCl ++ show b
    dprint (DataSig _ _ _ _ _) = "DataSig"
    dprint (Data _ ind n lbs me tss) = "Data " ++ show ind ++ " " ++ dprint n 
                                        ++ " " ++ dprints lbs ++ " " ++ dprint me 
                                        ++ " " ++ dprints tss
    dprint (RecordSig _ _ _ _) = "RecordSig"
    dprint (Record _ _ _ _ _ _ _ _) = "Record"
    dprint (Infix fix names) = "Infix " ++ show fix ++ " " ++ dprints names
    dprint (Syntax _ _) = "Syntax"
    dprint (PatternSyn _ _ _ _) = "PatternSyn"
    dprint (Mutual _ _) = "Mutual"
    dprint (Abstract _ _) = "Abstract"
    dprint (Private _ _) = "Private"
    dprint (InstanceB _ _) = "InstanceB"
    dprint (Macro _ _) = "Macro"
    dprint (Postulate _ _) = "Postulate"
    dprint (Primitive _ _) = "Primitive"
    dprint (Open _ _ _) = "Open"
    dprint (Import _ _ _ _ _) = "Import"
    dprint (ModuleMacro _ _ _ _ _) = "ModuleMacro"
    dprint (Module _ name _ decls) = "Module " ++ dprint name ++ "\n[" ++
                                     foldr (\x acc -> dprint x ++ ",\n" ++ acc) "]" decls
    dprint (UnquoteDecl _ _ _) = "UnquoteDecl"
    dprint (UnquoteDef _ _ _) = "UnquoteDef"
    dprint (Pragma _) = "Pragma"

instance DebugPrint LHS where
    dprint (LHS ptrn wptrn rwptrn wexpr) = "(LHS " ++ dprint ptrn ++ " " ++ dprints wptrn 
                                           ++ " " ++ dprints rwptrn ++ " " ++ dprints wexpr
    dprint (Ellipsis _ _ _ _) = "Ellipsis"

instance DebugPrint a => DebugPrint (RHS' a) where
    dprint AbsurdRHS = "AbsurdRHS"
    dprint (RHS e) = "(RHS " ++ dprint e ++ ")"


instance DebugPrint Pattern where
    dprint (IdentP qn) = "(IdentP " ++ dprint qn ++ ")"
    dprint (QuoteP r) = "QuoteP"
    dprint (AppP ptrn nptrn) = error "AppP"
    dprint (RawAppP r ptrns) = "(RawpAppP " ++ dprints ptrns ++ ")"
    dprint (OpAppP _ qn sn nptrns) = error "OpAppP"
    dprint (HiddenP _ np) = error "HiddenP"
    dprint (InstanceP _ np) = error "InstanceP"
    dprint (ParenP _ p) = "(ParenP " ++ dprint p ++ ")"
    dprint (WildP _) = "WildP"
    dprint (AbsurdP _) = "AbsurdP"
    dprint (AsP _ n p) = "(AsP " ++ dprint n ++ " " ++ dprint p ++ ")"
    dprint (DotP _ e) = "(DotP " ++ dprint e ++ ")"
    dprint (LitP lit) = "(LitP " ++ dprint lit ++ ")"

instance DebugPrint a => DebugPrint (WhereClause' [a]) where
    dprint NoWhere = "NoWhere"
    dprint (AnyWhere decls) = "(AnyWhere " ++ dprints decls ++ ")"
    dprint (SomeWhere n decls) = "(SomeWhere " ++ dprint n ++ " " ++ dprints decls ++ ")"

instance DebugPrint a => DebugPrint (LamBinding' a) where
    dprint (DomainFree a bn) = "(DomainFree " ++ show a ++ " " ++ dprint bn ++ ")"
    dprint (DomainFull a) = "(DomainFull " ++ dprint a ++ ")"

instance DebugPrint BoundName where
    dprint (BName bn bl bf) = "(BName " ++ dprint bn ++ " " ++ dprint bl ++ " " ++ show bf ++ ")"

instance DebugPrint a => DebugPrint (TypedBindings' a) where
    dprint (TypedBindings _ arg) = "(TypedBindings " ++ dprint arg ++ ")"

instance DebugPrint a => DebugPrint (TypedBinding' a) where
    dprint (TBind r wHbnames e) = "(TBind " ++ dprints wHbnames ++ " " ++ dprint e ++ ")"
    dprint (TLet r decls) = "(TLet " ++ dprints decls ++ ")"

instance DebugPrint a => DebugPrint (Arg a) where
    dprint (Arg ainfo e) = "(Arg " ++ show ainfo ++ " " ++ dprint e ++ ")"

instance DebugPrint a => DebugPrint (WithHiding a) where
    dprint (WithHiding hiding a) = "(WithHiding " ++ show hiding ++ " " ++ dprint a ++ ")"

instance DebugPrint a => DebugPrint (Maybe a) where
    dprint Nothing = "Nothing"
    dprint (Just a) = "(Just " ++ dprint a ++ ")"

instance DebugPrint Expr where
    dprint (Ident q) = "(Ident " ++ dprint q ++ ")"
    dprint (Lit l) = "(Lit " ++ dprint l ++ ")"
    dprint (QuestionMark r n) = "(QuestionMark " ++ show n ++ ")"
    dprint (Underscore r s) = "Underscore"
    dprint (RawApp r exprs) = "(RawApp" ++ show (map dprint exprs) ++ ")"
    dprint (App r e ne) = ""--"(" ++ dprint e ++ " " ++ dprint ne ++ ")"
    dprint (OpApp r qn sn nargs) = ""--"(" ++ dprint qn ++ " " ++ (foldr (\x acc -> dprint x ++ acc) "" nargs) ++ ")"
    dprint (WithApp _ _ _) = "WithApp"
    dprint (HiddenArg _ ne) = "HiddenArg"
    dprint (InstanceArg _ ne) = "InstanceArg"
    dprint (Lam _ vars e) = "Lam"
    dprint (AbsurdLam _ hiding) = "AbsurdLam"
    dprint (ExtendedLam _ xs) = "ExtendedLam"
    dprint (Fun _ e1 e2) = "(Fun " ++ dprint e1 ++ " " ++ dprint e2 ++ ")"
    dprint (Pi telesc e) = "Pi"
    dprint (Set r) = "Set"
    dprint (Prop r) = "Prop"
    dprint (SetN r n) = "SetN"
    dprint (Rec r recAssigns) = "Rec"
    dprint (RecUpdate r e fieldAssigns) = "RecUpdate"
    dprint (Let r decls e) = "Let"
    dprint (Paren r e) = "Paren"
    dprint (Absurd r) = "Absurd"
    dprint (As r n e) = "As"
    dprint (Dot r e) = "Dot"
    dprint (ETel telesc) = "ETel"
    dprint (QuoteGoal r n e) = "QuoteGoal"
    dprint (QuoteContext r) = "QuoteContext"
    dprint (Quote r) = "Quote"
    dprint (QuoteTerm r) = "QuoteTerm"
    dprint (Tactic r e es) = "Tactic"
    dprint (Unquote r) = "UnQuote"
    dprint (DontCare e) = "Dontcare"
    dprint (Equal r e1 e2) = "Equal"

instance DebugPrint Literal where
    dprint (LitNat _ n) = show n
    dprint (LitFloat _ fl) = show fl
    dprint (LitString _ s) = s
    dprint (LitChar _ c) = show c
    dprint (LitQName _ qn) = dprint qn
    dprint (LitMeta _ ap mid) = ""

instance DebugPrint QName where
    dprint (QName n) = dprint n

instance DebugPrint A.QName where
    dprint (A.QName _ name) = dprint name

instance DebugPrint A.Name where
    dprint (A.Name _ concr _ _) = dprint concr

instance DebugPrint Name where
    dprint (Name _ nameparts) = foldl (++) "" (map dprint nameparts)

instance DebugPrint NamePart where
    dprint (Id n) = n
    dprint (Hole) = "Hole"

instance DebugPrint (OpApp Expr) where
    dprint (Ordinary e) = dprint e
    dprint (SyntaxBindingLambda r vars e) = "(\\" ++ foldr ((++) . show ) "" vars ++ " -> " ++ dprint e ++ ")"