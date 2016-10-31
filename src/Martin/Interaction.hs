{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeSynonymInstances  #-}
{-# LANGUAGE UndecidableInstances  #-}
module Martin.Interaction where

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

import           Control.Exception
import           Control.Lens
import           Control.Monad.Except
import           Control.Monad.Reader
import           Control.Monad.State.Strict
import           Control.Monad.Writer
import qualified Data.List                                  as List
import           Data.Maybe
import           Data.Validation
import           Text.Printf

import qualified Martin.Agda.MakeCaseModified               as MC
import qualified Martin.Agda.Translation                    as T
import qualified Martin.Agda.Util                           as AU
import qualified Martin.Auto.ProofSearch                    as Ps
import qualified Martin.Strategy                            as S

-- | An exercise is just an Agda file, represented by the declarations inside it.
-- INVARIANT: this state needs to be kept in sync with the TCM state.
-- To prevent headaches, only modify the list of declarations (aka the user program)
-- when the changes have been type checked and the TCM state has been populated with
-- the declarations.
data ExerciseState = ExerciseState
  { _exerciseProgram   :: S.StatefulProgram
  -- ^ the current state of the program
  , _exerciseStrategy  :: S.ExerciseStrategy
  -- ^ the strategy for solving the current program
  , _exerciseUndo      :: [(S.StatefulProgram, S.ExerciseStrategy)]
  -- ^ a history of program states
  , _exerciseHintLevel :: Int
  -- ^ the current level of detail for hints
  }

makeLenses ''ExerciseState

-- | Environment for exercise computation.
data ExerciseEnv = ExerciseEnv
  { _exerciseFile    :: AbsolutePath
  -- ^ the exercise file we have loaded
  , _exerciseTCState :: TCState
  -- ^ the initial state of the type checker
  , _exerciseTCEnv   :: TCEnv
  -- ^ the default environment for the type checker
  , _exerciseSession :: S.Session
  -- ^ the Agda session for generating strategies
  }

makeLenses ''ExerciseEnv

-- | A prettified type checker error.
newtype PrettyTCErr = PrettyTCErr { getPrettyTCErr :: String }
  deriving (Show)
instance Exception PrettyTCErr

-- | Feedback given to user interaction.
type Feedback = [String]

makeFeedback :: String -> Feedback
makeFeedback = return

noFeedback :: Feedback
noFeedback = []

-- | Computes a hint for the given hole with the desired level of detail.
-- Currently, 0 means the least amount of detail and 2 is the highest.
giveHint :: (MonadState ExerciseState m, MonadReader ExerciseEnv m, MonadIO m)
         => InteractionId -> Int -> m Feedback
giveHint ii hintLevel = do
  st <- getStrategyFor ii
  tcs <- use $ exerciseProgram . S.programTCState
  return <$> case st of
    Nothing -> return "No hints available!"
    Just (S.RefineStrategy prf)
      | hintLevel == 0 -> return "Refine."
      | hintLevel == 1 -> do
          ((goal,hdb),_) <- runTCMEx tcs $ T.goalAndRules ii
          let candidates = map Ps.ruleName $ filter (Ps.canUnify goal . Ps.ruleConclusion) hdb
          return $ "Refine with a variable or a function returning the right type:\n"
            ++ List.intercalate ", " candidates ++ "."
      | otherwise -> return $ "Refine with '" ++ Ps.proofRule prf ++ "'."
    Just (S.SplitStrategy var _)
      | hintLevel == 0 -> return "Case-split."
      | hintLevel == 1 -> do
          (vars, _) <- runTCMEx tcs $ map show <$> AU.varsInScope ii
          return $ "Split one of the variables in the patterns on the left hand side:\n"
            ++ List.intercalate ", " vars ++ "."
      | otherwise ->  return $ "Split variable '" ++ var ++ "'."


-- | Retrieves the strategy for the given hole from the state.
getStrategyFor :: (MonadState ExerciseState m)
               => InteractionId -> m (Maybe S.ClauseStrategy)
getStrategyFor ii = getFirst <$> use (exerciseStrategy . ix (interactionId ii) . to First)

-- | Executes a split action.
splitUser :: (MonadState ExerciseState m, MonadReader ExerciseEnv m, MonadIO m)
          => InteractionId -> String -> m Feedback
splitUser ii var = do
  prog <- use exerciseProgram
  -- invoke case splitting functionality
  ((_, newClauses), _) <- runTCMEx (view S.programTCState prog) $ MC.makeCase ii noRange var
  let newDecls = AU.replaceClauses ii newClauses (view S.programDecls prog)
  --
  checkProgramAndUpdate newDecls
  -- check strategy
  st <- getStrategyFor ii
  let notWithStrat msg = do
        regenerateStrategy
        return $ makeFeedback msg
  case st of
    Just (S.SplitStrategy sv cs)
      | sv == var -> do
        exerciseStrategy %= concatReplace (interactionId ii) (map Just cs)
        return $ makeFeedback "Correct!"
      | otherwise -> notWithStrat "I chose to split on a different variable here."
    Just (S.RefineStrategy _) -> notWithStrat "I chose to refine here."
    Nothing -> notWithStrat $ "I didn't know what to do here. " ++
      "I cannot guarantee you can solve the exercise that way, though it might still be possible."

-- | Executes a refinement action.
refineUser :: (MonadState ExerciseState m, MonadReader ExerciseEnv m, MonadIO m)
           => InteractionId -> String -> m Feedback
refineUser ii def = do
  prog <- use exerciseProgram
  (expr, _) <- runTCMEx (view S.programTCState prog) $ do
    -- parse the user input in the given context
    given <- B.parseExprIn ii noRange def
    -- try to refine the hole with the user expression
    B.refine ii Nothing given >>= T.constructorFormA
  let newDecls = AU.replaceHole ii expr (view S.programDecls prog)
  checkProgramAndUpdate newDecls
  -- check strategy
  st <- getStrategyFor ii
  case st of
    Just (S.RefineStrategy prf) -> case stripPrefixFromProof expr prf of
      AccFailure fb -> regenerateStrategy >> return fb
      AccSuccess prfs -> do
        exerciseStrategy %= concatReplace (interactionId ii) (map (Just . S.RefineStrategy) prfs)
        return $ makeFeedback "Correct!"
    Just (S.SplitStrategy _ _) ->
      regenerateStrategy >> return (makeFeedback "I chose to split.")
    _ -> regenerateStrategy >> return (makeFeedback "I didn't know what to do here.")

-- | Given an expression, it checks whether that expression is a prefix of the given
-- proof and returns the sub-proofs that coincide with question marks in the expression.
stripPrefixFromProof :: A.Expr -> Ps.Proof -> AccValidation Feedback [Ps.Proof]
stripPrefixFromProof = go where
  -- ignore these
  go (A.ScopedExpr _ e) prf = go e prf
  -- try to parse other expressions as applications
  go e prf = case T.flattenVisibleApp e of
    A.Var v : args -> checkApp (prettyShow v) args prf
    A.Def d : args -> checkApp (T.qNameS d) args prf
    A.Con c : args -> checkApp (T.qNameS $ head $ A.unAmbQ c) args prf
    A.QuestionMark _ _ : args
      | null args -> pure [prf]
      | otherwise -> cons prf <$> checkApp (Ps.proofRule prf) args prf
    _ -> AccFailure $ makeFeedback "You have used a syntax that is not supported by this tutoring system."

  checkApp fname args prf
    | fname /= Ps.proofRule prf =
        AccFailure $ makeFeedback $ printf "You used '%s' where I used '%s'." fname (Ps.proofRule prf)
    | length args /= length (Ps.proofArgs prf) =
        AccFailure $ makeFeedback
        $ printf "You applied '%s' too a different number of arguments (%d) than I did (%d)."
            fname (length args) (length $ Ps.proofArgs prf)
    | otherwise = concat <$> zipWithM go args (Ps.proofArgs prf)

-- | Type checks a program and updates the current program state
-- with the new program and TCState if successful.
-- The previous state is recorded in the undo-history.
checkProgramAndUpdate :: (MonadState ExerciseState m, MonadReader ExerciseEnv m, MonadIO m)
                      => [A.Declaration] -> m ()
checkProgramAndUpdate newDecls = do
  tcs <- view exerciseTCState
  (newDecls', progState) <- runTCMEx tcs $ do
    -- rebuild interaction points (normally only created when going from concrete -> abstract)
    (newDecls', _) <- AU.rebuildInteractionPoints newDecls
    -- check updated AST (might not succeed if the termination checker intervenes)
    checkDecls newDecls'
    unfreezeMetas
    return newDecls'
  checkpoint
  exerciseProgram .= S.StatefulProgram newDecls' progState

-- | Regenerates the strategy for the current program state.
regenerateStrategy :: (MonadState ExerciseState m, MonadReader ExerciseEnv m, MonadIO m) => m ()
regenerateStrategy = do
  decls <- use $ exerciseProgram . S.programDecls
  strat <- view exerciseSession >>= \s -> liftIO $ S.buildStrategy s decls
  exerciseStrategy .= fromMaybe [] strat

-- | @concatReplace i rs xs@ replaces the i-th element of @xs@ with @rs@.
concatReplace :: Int -> [a] -> [a] -> [a]
concatReplace n _ []
  | n < 0 = []
concatReplace n repl (x:xs)
  | n == 0 = repl ++ xs
  | n > 0 = x : concatReplace (n - 1) repl xs
concatReplace _ _ _ = error "concatReplace: invalid arguments"

-- | Reverts the program and strategy state to the previous undo-checkpoint.
undo :: MonadState ExerciseState m => m Bool
undo = use exerciseUndo >>= \case
  [] -> return False
  (prog,strat):rest -> do
    exerciseUndo .= rest
    exerciseProgram .= prog
    exerciseStrategy .= strat
    return True

-- | Adds the current program and TCM state to the undo history.
checkpoint :: MonadState ExerciseState m => m ()
checkpoint = do
  step <- (,) <$> use exerciseProgram <*> use exerciseStrategy
  exerciseUndo %= cons step

-- | Displays the current state of the program to the user.
-- It also shows the numbers (InteractionId) of each hole. Based on that, the user can then
-- choose to perform an action on a given hole.
prettyProgram :: (MonadState ExerciseState m, MonadReader ExerciseEnv m, MonadIO m)
              => m String
prettyProgram = do
  prog <- use exerciseProgram
  fmap fst $ runTCMEx (view S.programTCState prog) $ do
    let decls = AU.setMetaNumbersToInteraction (view S.programDecls prog)
    render . vcat <$> mapM prettyA decls

-- | Runs a TCM computation inside the exercise monad.
-- All TCErr exceptions are converted to PrettyTCErr exceptions before
-- being rethrown outside of the TCM monad.
runTCMEx :: (MonadReader ExerciseEnv m, MonadIO m) => TCState -> TCM a -> m (a, TCState)
runTCMEx tcs tcm = do
  env <- view exerciseTCEnv
  liftIO $ runTCM env tcs $ tcm `catchError` (prettyError >=> liftIO . throwIO . PrettyTCErr)

runExerciseM :: ExerciseEnv -> ExerciseState -> (ReaderT ExerciseEnv (StateT ExerciseState IO) a) -> IO (a,ExerciseState)
runExerciseM exEnv exState m = runStateT (runReaderT m exEnv) exState

initExercise :: Int -> FilePath -> IO (Either String (ExerciseEnv, ExerciseState))
initExercise verbosity agdaFile = do
  -- load the Agda file-
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

    return (initialState, abstractDecls)
  case ret of
    Left err -> return . Left $ "Exercise session failed with\n%s\n" ++ err
    Right (initialState, decls) -> do
      session <- S.initSession verbosity absPath
      Just str <- S.buildStrategy session decls

      let exEnv = ExerciseEnv
            { _exerciseFile = absPath
            , _exerciseTCState = initialState
            , _exerciseTCEnv = initEnv { envCurrentPath = Just absPath }
            , _exerciseSession = session
            }
          exState = ExerciseState
            { _exerciseProgram = S.StatefulProgram decls progState
            , _exerciseStrategy = str
            , _exerciseUndo = []
            , _exerciseHintLevel = 0
            }
      return $ Right (exEnv, exState)
