{-# LANGUAGE FlexibleContexts #-}
module Main where


import           Strategy
import qualified Options.Applicative as OA
import           System.IO
import           Text.Printf
import Data.Monoid


data MartinOpt = MartinOpt
  { agdaFile :: FilePath
  , runMode  :: Mode
  }

data Mode = Interactive | Batch

progOptionParser :: OA.Parser MartinOpt
progOptionParser = MartinOpt
  <$> OA.argument OA.str
        (OA.metavar "FILE"
         <> OA.help "Path of the Agda file containing the exercise")
  <*> pure Interactive

main :: IO ()
main = undefined

-- main :: IO ()
-- main = OA.execParser opts >>= runMartin
--   where
--     opts = OA.info (OA.helper <*> progOptionParser)
--       ( OA.fullDesc
--       <> OA.progDesc "Run the tutor on the Agda exercise in FILE"
--       <> OA.header "martin - an interactive Agda tutor"
--       )
