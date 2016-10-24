{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}

module Lib
    ( someFunc
    ) where

import qualified Agda.Syntax.Abstract as A
import Agda.Syntax.Translation.ConcreteToAbstract
import Agda.Syntax.Translation.AbstractToConcrete
import Agda.TheTypeChecker
import Agda.Syntax.Concrete
import Agda.Syntax.Common
import Agda.Main
import Agda.Syntax.Parser
import Agda.Syntax.Literal
import Agda.Syntax.Fixity
import Agda.Utils.FileName
import Control.Monad.IO.Class
import Control.Monad.State.Strict
import Control.DeepSeq

import Agda.Syntax.Abstract.Pretty

import ProofSearch
import SearchTree
import Translation

-- Two ways of parsing agda programs
-- Either we parse a full agda program from a file
-- or we parse a given expression

-- The Agda library contains a pretty printer, which can be
-- called with show

--Add individual paths
pt = "/mnt/win/Documenten/CS/TFL/martin/examples/Example2.agda"
pathFer = "/home/ferdinand/University/TFL/martin/examples/Example2.agda"

pt1 = parseFile' moduleParser (mkAbsolute pt)

someFunc :: IO ()
someFunc = do
    -- Parse an agda file and debugprint it
    -- Requires the path to be absolute
    let path = pathFer
    s <- parseFile' moduleParser (mkAbsolute path)
    runTCMPrettyErrors $ test (snd s)
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
    checkDecls abstr
    --liftIO $ putStrLn "abstr"
    --liftIO $ putStrLn $ show abstr
    proof <- getGoal abstr 1
    (hdb,_) <- runStateT (makeRules abstr) []
    --let (hdb,_) = runStateT (makeRules abstr) []
    liftIO $ putStrLn $ printRules hdb
    e <- proofToAbstract (head proof) hdb 0
    liftIO $ putStrLn $ show e
    --liftIO $ putStrLn $ show proof
    --liftIO $ putStrLn $ show e
    --liftIO $ putStrLn pretty
    --conctr' <- runAbsToCon $ toConcrete abstr
    --liftIO $ putStrLn $ dprint $ head conctr'
    --check <- checkDecls abstr    
    --liftIO $ putStrLn $ show check
    return ()

getGoal abstr n = do
    (mps,_) <- runStateT (pipeline abstr n) [] 
    return mps

pipeline abstr n = do
    hdb <- makeRules abstr
    g <- generateGoal n abstr
    
    if null g
        then return []
        else do
            liftIO $ putStrLn $ "goal: " ++ show (head g)
            return $ dfs $ cutoff 2 $ solve (head g) hdb


printRules :: HintDB -> String
printRules [] = ""
printRules (x:xs) = show x ++ "\n" ++ printRules xs


