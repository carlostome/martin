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
import qualified Martin.Interaction as I

-- | Runs an interactive user session, loading the given exercise
-- This should be the main entry point for everything having to do with Agda.
runStrategyGenerator :: AU.AgdaOptions -> FilePath -> IO ()
runStrategyGenerator opts agdaFile = do
  ret <- I.initExercise opts agdaFile
  case ret of
    Left err -> printf "Failed to generate strategy:\n%s\n" err
    Right (_, st) -> do
      let strat = view I.exerciseStrategy st
      forM_ (zip [0..] strat) $ \(ii,s) -> do
        printf "For hole ?%d\n" (ii :: Int)
        printf "  %s" $ maybe "We were not able to generate a strategy" S.prettyStrategy s

