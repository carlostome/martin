module AgdaStrategy where

import           Control.Lens
import           Control.Monad.Except
import           Text.Printf

import qualified Martin.Agda.Util                           as AU
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
        printf "  %s\n" $ maybe "We were not able to generate a strategy" S.prettyStrategy s

