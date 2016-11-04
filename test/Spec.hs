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
import           Text.Printf

import qualified Martin.Agda.Lens        as AL
import qualified Martin.Agda.Util        as AU
import qualified Martin.Interaction      as I
import qualified Martin.Strategy         as S

-- auto-generated module by cabal, used for accessing data files
import           Paths_martin

initTestExercise :: FilePath -> IO (Either String (I.ExerciseEnv, I.ExerciseState))
initTestExercise agdaFile = do
  absFile <- getDataFileName agdaFile
  let opts = AU.defaultAgdaOptions
        & AU.agdaOptIncludePaths .~ [takeDirectory absFile]
  I.initExercise opts absFile


canSolve :: FilePath -> IO ()
canSolve agdaFile = do
  ret <- initTestExercise agdaFile
  case ret of
    Left str -> expectationFailure str
    Right (exEnv, exState) -> do
      let decls = view (I.exerciseProgram . S.programDecls) exState
          progHoles = toListOf (traverse . AL.questionMarks) decls
          strat = view I.exerciseStrategy exState
      if | length progHoles /= length strat -> expectationFailure "Number of holes and clause strategies differ"
         | any isNothing strat -> expectationFailure "Not all clauses could be solved"
         | otherwise -> do
             -- try if we can actually apply the generated strategy
             let apply = views I.exerciseSession S.applyStrategy exEnv
             sol <- apply decls strat
             case sol of
               Left str -> expectationFailure $ printf "Could not apply strategy:\n%s" ++ str
               Right prog
                 | has (traverse . AL.questionMarks) prog -> expectationFailure "Not all clauses have been solved"
                 | otherwise -> return ()

testCases :: [(String,FilePath)]
testCases =
  [ ("id : A -> A", "test-files/Id.agda")
  , ("absurd : Empty -> A", "test-files/Absurd.agda")
  , ("map : (A -> B) -> Vec A n -> Vec B n", "test-files/VecMap.agda")
  , ("replicate : (n : Nat) -> A -> Vec A n", "test-files/VecReplicate.agda")
  , ("append : Vec A m -> Vec A n -> Vec A (add m n)", "test-files/VecAppend.agda")
  , ("member? : ((x y : A) -> Dec (x == y)) -> (v : A) -> (vs : List A) -> Dec (Member v vs)", "test-files/ListMember.agda")
  , ("member? : ((x y : A) -> Dec (x == y)) -> (v : A) -> (vs : Vec A n) -> Dec (Member v vs)", "test-files/VecMember.agda")
  ]

main :: IO ()
main = hspec $ do
  describe "Can find strategy for" $ do
    forM_ testCases $ \(name, path) -> it name $ canSolve path
