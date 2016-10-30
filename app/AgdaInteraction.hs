{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeSynonymInstances  #-}
{-# LANGUAGE UndecidableInstances  #-}
module AgdaInteraction where

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

import qualified MakeCaseModified                           as MC

import           Control.DeepSeq
import           Control.Lens
import           Control.Monad.Except
import           Control.Monad.IO.Class
import           Control.Monad.Reader
import           Control.Monad.State.Strict
import           Control.Monad.Writer
import qualified Data.List                                  as List
import qualified Data.Set                                   as Set
import           Debug.Trace
import           System.Console.Haskeline
import qualified System.Console.Haskeline                   as HaskEx
import           System.FilePath                            ((</>))
import qualified Text.ParserCombinators.ReadP               as ReadP
import qualified Text.ParserCombinators.ReadPrec            as ReadPrec
import           Text.Printf
import           Text.Read                                  (readPrec)
import           Data.Generics.Geniplate
import           Data.List                                  ((\\))
import           Data.Maybe
import           Data.Monoid

import           SearchTree
import qualified AgdaUtil                                   as AU
import qualified Strategy                                   as S
import qualified ProofSearch                                   as Ps
import qualified Translation                                   as T

-- | An exercise is just an Agda file, represented by the declarations inside it.
-- INVARIANT: this state needs to be kept in sync with the TCM state.
-- To prevent headaches, only modify the list of declarations (aka the user program)
-- when the changes have been type checked and the TCM state has been populated with
-- the declarations.
data ExerciseState = ExerciseState
  { _exerciseProgram  :: S.StatefulProgram
  -- ^ the current state of the program
  , _exerciseStrategy :: S.ExerciseStrategy
  , _exerciseUndo     :: [(S.StatefulProgram, S.ExerciseStrategy)]
  -- ^ a history of program states
  }

makeLenses ''ExerciseState

-- | Environment for exercise computation.
data ExerciseEnv = ExerciseEnv
  { _exerciseFile    :: AbsolutePath
  , _exerciseTCState :: TCState
  , _exerciseTCEnv   :: TCEnv
  , _exerciseSession :: S.Session
  }

makeLenses ''ExerciseEnv

newtype PrettyTCErr = PrettyTCErr { getPrettyTCErr :: String }
  deriving (Show)

instance Exception PrettyTCErr

-- | I'm sorry for another Monad stack, but somewhere we need to keep track of
-- information related to the exercise session.
type ExerciseM = InputT (ReaderT ExerciseEnv (StateT ExerciseState IO))

-- * Interfacing with User

-- | Runs an interactive user session, loading the given exercise
-- This should be the main entry point for everything having to do with Agda.
runInteractiveSession :: Int -> FilePath -> IO ()
runInteractiveSession verbosity agdaFile = do
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

    return (initialState, abstractDecls)
  case ret of
    Left err -> printf "Exercise session failed with\n%s\n" err
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
            }

      putStrLn $ unlines
        [ "Welcome to Martin - the interactive Agda tutor"
        , "You have loaded exercise " ++ show absPath
        , "Type `h` to get help!"
        , ""
        ]

      let go = do
            prettyProgram >>= outputStrLn
            outputStrLn ""
            exerciseLoop
      void $ runStateT (runReaderT (runInputT defaultSettings go) exEnv) exState

data TopCommand
  = CmdTopUndo
  | CmdTopSelect Int
  | CmdTopExit
  | CmdTopHelp
  | CmdTopPrint
  deriving (Eq, Ord, Show, Read)

data HoleCommand
  = CmdHoleType
  | CmdHoleContext
  | CmdRefine String
  | CmdSplit String
  | CmdHoleLeave
  | CmdHoleHint
  deriving (Eq, Ord, Show, Read)

readPTopCommand :: ReadP.ReadP TopCommand
readPTopCommand = msum
  [ CmdTopUndo <$ ReadP.char 'u'
  , CmdTopExit <$ ReadP.char 'q'
  , CmdTopHelp <$ ReadP.char 'h'
  , CmdTopPrint <$ ReadP.char 'p'
  , CmdTopSelect <$> (ReadP.char 's' *> ReadP.skipSpaces *> ReadPrec.readPrec_to_P readPrec 0)
  ]

readPHoleCommand :: ReadP.ReadP HoleCommand
readPHoleCommand = msum
  [ CmdHoleType <$ ReadP.char 't'
  , CmdHoleContext <$ ReadP.char 'c'
  , CmdHoleLeave <$ ReadP.char 'l'
  , CmdHoleHint <$ ReadP.char 'h'
  , CmdRefine <$> (ReadP.char 'r' *> ReadP.skipSpaces *> ReadP.many1 ReadP.get)
  , CmdSplit <$> (ReadP.char 's' *> ReadP.skipSpaces *> ReadP.many1 ReadP.get)
  ]

runReadP :: ReadP.ReadP a -> String -> Maybe a
runReadP p s =
  case [ x | (x,"") <- ReadPrec.readPrec_to_S (ReadPrec.lift p) 0 s ] of
    [x] -> Just x
    _   -> Nothing

exerciseLoop :: ExerciseM ()
exerciseLoop = do
  tcs <- use $ exerciseProgram . S.programTCState
  (ips, _) <- runTCMEx tcs getInteractionPoints
  if null ips
    then outputStrLn "All goals have been solved, congratulations!"
    else do
    minput <- getInputLine "% "
    let cmd = maybe (Just CmdTopExit) (runReadP readPTopCommand) minput
    catchTCMErr exerciseLoop $ case cmd of
      Nothing -> do
        outputStrLn "Unknown command!"
        exerciseLoop
      Just CmdTopUndo -> do
        undo >>= \case
          True -> outputStrLn "Undone!"
          False -> outputStrLn "Cannot undo!"
        exerciseLoop
      Just CmdTopExit -> outputStrLn "Bye!"
      Just (CmdTopSelect hole) -> do
        let ii = InteractionId hole
        if ii `elem` ips then do
          outputStrLn $ "Focusing on hole " ++ show ii
          handle (\Interrupt -> return ()) $ withInterrupt $ holeLoop ii
          else
          outputStrLn "A hole with this number does not exist!"
        exerciseLoop
      Just CmdTopHelp -> do
        outputStrLn $ unlines
          [ "Available commands at the top level:"
          , "  h          print this help"
          , "  u          undo last step"
          , "  s <hole>   select hole with number <hole>"
          , "  p          print the program"
          , "  q          quit program"
          , ""
          , "Available commands in a hole"
          , "  l          leave the hole"
          , "  t          print the type of the hole"
          , "  c          print the context of the hole"
          , "  r <def>    refine the hole with definition <def>"
          , "  s <var>    split variable <var>"
          ]
        exerciseLoop
      Just CmdTopPrint -> do
        prettyProgram >>= outputStrLn
        exerciseLoop

catchTCMErr :: MonadException m => InputT m a -> InputT m a -> InputT m a
catchTCMErr cont act = HaskEx.catch act $ \e -> do
  outputStrLn "Agda returned an error:\n"
  outputStrLn $ getPrettyTCErr e
  cont

holeLoop :: InteractionId -> ExerciseM ()
holeLoop ii = do
  minput <- getInputLine $ show ii ++ "% "
  let cmd = maybe (Just CmdHoleLeave) (runReadP readPHoleCommand) minput
  catchTCMErr (holeLoop ii) $ case cmd of
    Nothing -> do
      outputStrLn "Unknown command!"
      holeLoop ii
    Just CmdHoleLeave -> return ()
    Just CmdHoleType -> do
      tcs <- use $ exerciseProgram . S.programTCState
      (doc, _) <- runTCMEx tcs $ B.typeOfMeta B.Normalised ii >>= \(B.OfType _ ty) -> prettyA ty
      outputStrLn $ render doc
      holeLoop ii
    Just CmdHoleContext -> do
      tcs <- use $ exerciseProgram . S.programTCState
      let prettyCtx (name, ty) = do
            let pname = pretty $ either id A.qnameName name
            pty <- prettyA ty
            return $ pname <+> char ':' <+> pty
      (doc, _) <- runTCMEx tcs $ AU.thingsInScopeWithType ii >>= mapM prettyCtx
      outputStrLn $ render $ vcat doc
      holeLoop ii
    Just (CmdSplit var) -> splitUser ii var
    Just (CmdRefine def) -> refineUser ii def
    Just CmdHoleHint -> do
      st <- getStrategyFor ii
      case st of
        Nothing -> outputStrLn "No hints available!"
        Just (S.RefineStrategy prf) ->
          outputStrLn $ "Refine with '" ++ Ps.proofRule prf ++ "'"
        Just (S.SplitStrategy var _) ->
          outputStrLn $ "Split variable '" ++ var ++ "'"
      holeLoop ii

getStrategyFor :: InteractionId -> ExerciseM (Maybe S.ClauseStrategy)
getStrategyFor ii = getFirst <$> use (exerciseStrategy . ix (interactionId ii) . to First)

splitUser :: InteractionId -> String -> ExerciseM ()
splitUser ii var = do
  prog <- use exerciseProgram
  -- invoke case splitting functionality
  ((_, newClauses), _) <- runTCMEx (view S.programTCState prog) $ MC.makeCase ii noRange var
  let newDecls = AU.replaceClauses ii newClauses (view S.programDecls prog)
  --
  updateProgramAndCheck newDecls
  -- check strategy
  st <- getStrategyFor ii
  let notWithStrat msg = outputStrLn msg >> regenerateStrategy
  case st of
    Just (S.SplitStrategy sv cs)
      | sv == var ->
        exerciseStrategy %= concatReplace (interactionId ii) (map Just cs)
      | otherwise -> notWithStrat "I chose to split on a different variable here."
    Just (S.RefineStrategy _) -> notWithStrat "I chose to refine here."
    Nothing -> notWithStrat "I didn't know what to do here."

refineUser :: InteractionId -> String -> ExerciseM ()
refineUser ii def = do
  prog <- use exerciseProgram
  (expr, _) <- runTCMEx (view S.programTCState prog) $ do
    -- parse the user input in the given context
    given <- B.parseExprIn ii noRange def
    -- try to refine the hole with the user expression
    B.refine ii Nothing given
  let newDecls = AU.replaceHole ii expr (view S.programDecls prog)
  updateProgramAndCheck newDecls
  -- check strategy
  st <- getStrategyFor ii
  -- TODO: do not regenerate strategy if the user actually did what we expected
  case st of
    --Just (S.RefineStrategy prf) -> _
    _ -> regenerateStrategy

updateProgramAndCheck :: [A.Declaration] -> ExerciseM ()
updateProgramAndCheck newDecls = do
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

regenerateStrategy :: ExerciseM ()
regenerateStrategy = do
  decls <- use $ exerciseProgram . S.programDecls
  strat <- view exerciseSession >>= \s -> liftIO $ S.buildStrategy s decls
  exerciseStrategy .= fromMaybe [] strat

concatReplace :: Int -> [a] -> [a] -> [a]
concatReplace n repl []
  | n < 0 = []
concatReplace n repl (x:xs)
  | n == 0 = repl ++ xs
  | n > 0 = x : concatReplace (n - 1) repl xs
concatReplace _ _ _ = error "concatReplace: invalid arguments"

undo :: ExerciseM Bool
undo = use exerciseUndo >>= \case
  [] -> return False
  (prog,strat):rest -> do
    exerciseUndo .= rest
    exerciseProgram .= prog
    exerciseStrategy .= strat
    return True

-- | Adds the current program and TCM state to the undo history.
checkpoint :: ExerciseM ()
checkpoint = do
  step <- (,) <$> use exerciseProgram <*> use exerciseStrategy
  exerciseUndo %= cons step

-- | Displays the current state of the program to the user.
-- It also shows the numbers (InteractionId) of each hole. Based on that, the user can then
-- choose to perform an action on a given hole.
prettyProgram :: ExerciseM String
prettyProgram = do
  prog <- use exerciseProgram
  fmap fst $ runTCMEx (view S.programTCState prog) $ do
    let decls = AU.setMetaNumbersToInteraction (view S.programDecls prog)
    render . vcat <$> mapM prettyA decls

runTCMEx :: TCState -> TCM a -> ExerciseM (a, TCState)
runTCMEx tcs tcm = do
  env <- view exerciseTCEnv
  liftIO $ runTCM env tcs $ tcm `catchError` (prettyError >=> HaskEx.throwIO . PrettyTCErr)

    -- -- run user session
    -- st <- execStateT (runReaderT exerciseSession exEnv) exState
    -- -- if all went well, st contains the solved exercise
    -- -- TODO: pretty print and send to teacher ;)
    -- return ()
  -- -- print errors
{-


-- | Type checks a new state of the program and update, if successful.
-- May fail with an exception if any step goes wrong. Restoring state
-- should be handled by caller.
performUserAction :: InteractionId -> UserAction -> ExerciseM ()
performUserAction hole action = do
  -- apply action to generate new program
  newprog <- case action of
    UserRefine estr -> do
      -- parse the user input in the given context
      given <- tcmToEx $ B.parseExprIn hole noRange estr
      -- try to refine the hole with the user expression
      expr <- tcmToEx $ B.give hole Nothing given
      -- replace hole in AST
      replaceHole hole expr <$> gets exerciseDecls
    UserSplit var -> do
      -- invoke case splitting functionality
      (ctx, newClauses) <- tcmToEx $ MC.makeCase hole noRange var
      -- ctx seems only to be relevant when splitting in extended lambdas, not something we do
      replaceClauses hole newClauses <$> gets exerciseDecls
  -- type check
  resetTCState
  -- rebuild interaction points (normally only created when going from concrete -> abstract)
  newprog' <- rebuildInteractionPoints newprog
  -- check updated AST (might not succeed if the termination checker intervenes)
  tcmToEx $ do
    checkDecls newprog'
    unfreezeMetas
  modify $ \s -> s { exerciseDecls = newprog' }

undo :: ExerciseM Bool
undo = do
  hist <- gets exerciseUndo
  case hist of
    (prog,st):rest -> do
      restoreTCState st
      tcmToEx $ getInteractionIdsAndMetas >>= liftIO . print
      modify $ \s -> s { exerciseUndo = rest, exerciseDecls = prog }
      return True
    _ -> return False

-- | Takes a proof and converts it to an abstract expression in the context of the given hole.
proofToAbstractExpr :: InteractionId -> Proof -> TCM A.Expr
proofToAbstractExpr ii proof = B.parseExprIn ii noRange (proofStr proof) where
  proofStr (Proof name args _)
    | List.null args = name
    | otherwise = "(" ++ List.unwords (name : map proofStr args) ++ ")"

-- | Replaces a hole identified by its interaction id with a new expression.
replaceHole :: A.ExprLike e => InteractionId -> A.Expr -> e -> e
replaceHole ii repl = A.mapExpr $ \e -> case e of
                                  A.QuestionMark _ iiq
                                    | iiq == ii -> repl
                                  other -> other
-- | Replaces all question marks with fresh interaction points and registers them with the type checker.
-- This step is necessary after resetting the type checker state.
rebuildInteractionPoints :: A.ExprLike e => e -> ExerciseM e
rebuildInteractionPoints = tcmToEx . A.traverseExpr go where
  go (A.QuestionMark m _) = A.QuestionMark m <$> registerInteractionPoint noRange Nothing
  go other = return other

-- | Reverts to a fresh Agda TCM state, forgetting all user definitions and retaining only the primitives
resetTCState :: ExerciseM ()
resetTCState = asks exerciseInitialAgdaState >>= restoreTCState

-- | Lift a TCM computation in the exercise monad.
-- Can't use 'MonadTCM' because that requires reader and state over
-- the TCM env and state and not our state.
tcmToEx :: TCM a -> ExerciseM a
tcmToEx = lift . lift

-- | Try a computation, executing either the success handler with the result
-- or the error handler with the caught exception.
tryIt :: MonadError e m => m a -> (a -> m b) -> (e -> m b) -> m b
tryIt act success failure = do
  r <- fmap Right act `catchError` \e -> return $ Left e
  either failure success r

-- | Returns the current TCM state.
saveTCState :: ExerciseM TCState
saveTCState = tcmToEx get

-- | Restores the TCM state.
restoreTCState :: TCState -> ExerciseM ()
restoreTCState = tcmToEx . put

-- | Displays the current state of the program to the user.
-- It also shows the numbers (InteractionId) of each hole. Based on that, the user can then
-- choose to perform an action on a given hole.
showProgramToUser :: ExerciseM ()
showProgramToUser = do
    prog <- setMetaNumbersToInteraction <$> gets exerciseDecls
    doc <- tcmToEx $ vcat <$> mapM prettyA prog  -- printDecls prog
    liftIO $ putStrLn $ render doc

refineWithProof :: InteractionId -> Proof -> ExerciseM ()
refineWithProof hole proof = return ()

-- * Interfacing with Agda


-- | This initializes the TCM state just enough to get everything started.
-- For now, it uses the default options and loads Agda's Level primitives.
initAgda :: Int -> TCM TCState
initAgda verbosity = do
  -- initialize interactive state
  resetAllState
  setCommandLineOptions defaultOptions
    { optPragmaOptions = (optPragmaOptions defaultOptions)
      { optVerbose = Trie.singleton [] verbosity }
    }

  -- ==================== BEGIN CODE FROM AGDA SOURCE
  libdir <- liftIO defaultLibDir
  -- To allow posulating the built-ins, check the primitive module
  -- in unsafe mode
  _ <- bracket_ (gets Lens.getSafeMode) Lens.putSafeMode $ do
    Lens.putSafeMode False
    -- Turn off import-chasing messages.
    -- We have to modify the persistent verbosity setting, since
    -- getInterface resets the current verbosity settings to the persistent ones.
    bracket_ (gets Lens.getPersistentVerbosity) Lens.putPersistentVerbosity $ do
      Lens.modifyPersistentVerbosity (Trie.delete [])  -- set root verbosity to 0
      -- We don't want to generate highlighting information for Agda.Primitive.
      withHighlightingLevel None $ do
        primitiveModule <- moduleName $ mkAbsolute $
            libdir </> "prim" </> "Agda" </> "Primitive.agda"
        getInterface_ primitiveModule
  -- ==================== END CODE FROM AGDA SOURCE
  -- return with state right after initialization, to be able to speed up things when we need to reset
  get


-- * Some functions solely used for testing stuff

itest2 :: FilePath -> IO ()
itest2 agdaFile = do
  -- load agda file
  path <- absolute agdaFile
  (pragmas, concreteDecls) <- parseFile' moduleParser path
  -- run TCM computation (inside Agda's type checking monad)
  runTCMPrettyErrors $ do
    -- load primitives like Level etc.
    initialState <- initAgda 0
    -- convert to abstract syntax
    abstractDecls <- toAbstract concreteDecls
    checkDecls abstractDecls
    -- print all interaction metas (i.e. holes in the program)
    getInteractionIdsAndMetas >>= liftIO . print

    -- TEST CODE for map function
    [(inil,mnil), (icons,mcons)] <- getInteractionIdsAndMetas
    forM_ itWorks $ \prf -> do
      liftIO $ print prf
      given <- proofToAbstractExpr icons prf
      pp <- prettyA given
      liftIO $ print $ render pp
    -- END TEST CODE

    -- try restoring the state
    put initialState
    getInteractionIdsAndMetas >>= liftIO . print -- prints [], so restoring actually works

    return ()

-}


instance MonadState s m => MonadState s (InputT m) where
  get = lift get
  put = lift . put

instance MonadReader e m => MonadReader e (InputT m) where
  ask = lift ask
  local f = mapInputT (local f)
