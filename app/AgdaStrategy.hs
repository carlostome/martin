{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeSynonymInstances  #-}
{-# LANGUAGE UndecidableInstances  #-}
module AgdaStrategy where

import qualified Agda.Interaction.BasicOps                  as B
import qualified Agda.Syntax.Abstract                       as A
import           Agda.Syntax.Abstract.Pretty
import           Agda.Syntax.Common
import           Agda.Syntax.Position
import           Agda.Syntax.Translation.ConcreteToAbstract
import           Agda.TheTypeChecker
import           Agda.TypeChecking.Errors
import           Agda.TypeChecking.Monad
import           Agda.Utils.FileName
import           Agda.Utils.Pretty

import           Control.Lens
import           Control.Monad.Except
import           Control.Monad.Reader
import           Control.Monad.State.Strict
import           Control.Monad.Writer
import           Data.Maybe
import           System.Console.Haskeline
import qualified System.Console.Haskeline                   as HaskEx
import qualified Text.ParserCombinators.ReadP               as ReadP
import qualified Text.ParserCombinators.ReadPrec            as ReadPrec
import           Text.Printf
import           Text.Read                                  (readPrec)

import qualified Martin.Agda.MakeCaseModified               as MC
import qualified Martin.Agda.Util                           as AU
import qualified Martin.Auto.ProofSearch                    as Ps
import qualified Martin.Strategy                            as S

-- | Runs an interactive user session, loading the given exercise
-- This should be the main entry point for everything having to do with Agda.
runStrategyGenerator :: Int -> FilePath -> IO ()
runStrategyGenerator verbosity agdaFile = do
  -- load the Agda file
  (absPath, module') <- AU.parseAgdaFile agdaFile
  (ret, progState) <- runTCM initEnv initState
    $ local (\e -> e { envCurrentPath = Just absPath })
    $ flip catchError (prettyError >=> return . Left ) $ Right <$> do
    -- load Level primitives and setup TCM state
    initialState <- AU.initAgda verbosity -- the number is the verbosity level, useful for debugging
    -- REMARK: initialState should now contain a snapshot of an initialized Agda session and can be used to quickly
    -- revert when we need to recheck the exercise code.
    -- convert exercise to abstract syntax
    abstractDecls <- toAbstract module'
    -- check that the exercise is valid to begin with
    checkDecls abstractDecls
    unfreezeMetas

    ips <- getInteractionPoints
    return (ips, abstractDecls)
  case ret of
    Left err -> printf "Failed to load exercise file:\n%s\n" err
    Right (ips, decls) -> do
      session  <- S.initSession verbosity absPath
      Just str <- S.buildStrategy session decls
      forM_ (zip ips str) $ \(ii,strat) -> do
        putStrLn $ "For hole " ++ show ii
        putStrLn $ "  " ++ maybe "We were not able to generate a strategy" show strat

