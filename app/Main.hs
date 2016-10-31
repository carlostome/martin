{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TemplateHaskell #-}
module Main where

import           Strategy
import qualified Options.Applicative as OA
import           System.IO
import           Text.Printf
import Data.Monoid
import Control.Lens
import qualified AgdaInteraction as AI
import qualified AgdaStrategy as AS


data MartinOpt = MartinOpt
  { _agdaFile     :: FilePath
  , _onlyPrint    :: Bool
  }

makeLenses ''MartinOpt

progOptionParser :: OA.Parser MartinOpt
progOptionParser = MartinOpt
  <$> OA.argument OA.str
        (OA.metavar "FILE"
         <> OA.help "Path of the Agda file containing the exercise")
  <*> OA.switch (OA.short 'p' <>
                 OA.long "print" <>
                 OA.help "Print strategy and quit")

main :: IO ()
main = do
  options <- OA.execParser opts
  let file = view agdaFile options
  if view onlyPrint options
     then AS.runStrategyGenerator 0 file
     else AI.runInteractiveSession 0 file

  where
    opts = OA.info (OA.helper <*> progOptionParser)
      ( OA.fullDesc
      <> OA.progDesc "Run the tutor on the Agda exercise in FILE"
      <> OA.header "martin - an interactive Agda tutor"
      )
