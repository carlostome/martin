{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE MultiWayIf            #-}
import qualified Agda.Syntax.Abstract    as A
import           Agda.Syntax.Common
import           Agda.Syntax.Info

import           Control.Exception       (evaluate)
import           Control.Lens
import           Control.Monad
import           Control.Monad.IO.Class
import           Data.Generics.Geniplate
import           Data.Maybe
import           System.Directory
import           System.FilePath
import           Test.Hspec

import qualified Martin.Agda.Util        as AU
import qualified Martin.Interaction      as I
import qualified Martin.Strategy         as S

-- auto-generated module by cabal, used for accessing data files
import           Paths_martin

universeBiFold :: UniverseBi s t => Fold s t
universeBiFold = to universeBi . folded

_QuestionMark :: Prism A.Expr A.Expr (MetaInfo, InteractionId) (MetaInfo, InteractionId)
_QuestionMark = prism' (uncurry A.QuestionMark) $ \e -> case e of
  A.QuestionMark mi ii -> Just (mi, ii)
  _                    -> Nothing

initTestExercise :: FilePath -> IO (Either String (I.ExerciseEnv, I.ExerciseState))
initTestExercise agdaFile = do
  absFile <- getDataFileName agdaFile
  let opts = AU.defaultAgdaOptions
        & AU.agdaOptIncludePaths .~ [takeDirectory absFile]
  I.initExercise opts absFile

strategyShouldBe agdaFile strategy = do
  ret <- initTestExercise agdaFile
  case ret of
    Left str -> expectationFailure str
    Right (exEnv, exState) ->
      view I.exerciseStrategy exState `shouldBe` strategy


canSolve :: FilePath -> IO ()
canSolve agdaFile = do
  ret <- initTestExercise agdaFile
  case ret of
    Left str -> expectationFailure str
    Right (exEnv, exState) -> do
      let progHoles = toListOf (I.exerciseProgram . S.programDecls . folded . universeBiFold . _QuestionMark) exState
          strat = view I.exerciseStrategy exState
      if | length progHoles /= length strat -> expectationFailure "Number of holes and clause strategies differ"
         | any isNothing strat -> expectationFailure "Not all clauses could be solved"
         | otherwise -> return ()

testCases :: [(String,FilePath)]
testCases =
  [ ("map : (A -> B) -> Vec A n -> Vec B n", "test-files/VecMap.agda")
  , ("replicate : (n : Nat) -> A -> Vec A n", "test-files/VecReplicate.agda")
  , ("append : Vec A m -> Vec A n -> Vec A (add m n)", "test-files/VecAppend.agda")
  ]

main :: IO ()
main = hspec $ do
  describe "Can find strategy for" $ do
    forM_ testCases $ \(name, path) -> it name $ canSolve path
