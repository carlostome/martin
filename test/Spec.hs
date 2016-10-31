import Test.Hspec
import Control.Exception (evaluate)
import Control.Lens
import Control.Monad
import Control.Monad.IO.Class
import System.Directory
import System.FilePath

import qualified Martin.Interaction as I
import qualified Martin.Agda.Util as AU

import Paths_martin

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

canSolve agdaFile = do
  ret <- initTestExercise agdaFile
  case ret of
    Left str -> expectationFailure str
    Right (exEnv, exState) -> return ()

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
