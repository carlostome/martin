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
import Data.Maybe

import Agda.Syntax.Abstract.Pretty

import ProofSearch
import SearchTree
import Translation hiding (printRules)

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
    g <- getGoal abstr 0
    liftIO $ putStrLn $ show g
    return ()

getGoal abstr n = do
    (mps,_) <- runStateT (pipeline abstr n) [] 
    return mps

pipeline abstr n = do
    hdb <- makeRules abstr n
    liftIO $ putStrLn $ printRules hdb
    g <- generateGoal abstr n
    hdb' <- get
    liftIO $ putStrLn $ printRules hdb'
    
    if isNothing g
        then return []
        else do
            liftIO $ putStrLn $ show (fromJust g)
            return $ dfs $ cutoff 2 $ solve (fromJust g) hdb'


printRules :: HintDB -> String
printRules [] = ""
printRules (x:xs) = show x ++ "\n" ++ printRules xs
