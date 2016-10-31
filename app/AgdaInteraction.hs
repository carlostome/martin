{-# OPTIONS_GHC -fno-warn-orphans #-}
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
import qualified Agda.Syntax.Abstract.Pretty                as A
import           Agda.Syntax.Common
import           Agda.Syntax.Translation.ConcreteToAbstract
import           Agda.TheTypeChecker
import           Agda.TypeChecking.Errors
import           Agda.TypeChecking.Monad
import           Agda.Utils.Pretty

import           Control.Lens
import           Control.Monad.Except
import           Control.Monad.Reader
import           Control.Monad.State.Strict
import qualified Data.Map.Strict                            as Map
import           System.Console.Haskeline
import qualified System.Console.Haskeline                   as HaskEx
import qualified Text.ParserCombinators.ReadP               as ReadP
import qualified Text.ParserCombinators.ReadPrec            as ReadPrec
import           Text.Printf
import           Text.Read                                  (readPrec)

import qualified Martin.Agda.Util                           as AU
import           Martin.Interaction
import qualified Martin.Strategy                            as S

-- | I'm sorry for another Monad stack, but somewhere we need to keep track of
-- information related to the exercise session.
type ExerciseM = InputT (ReaderT ExerciseEnv (StateT ExerciseState IO))

-- * Interfacing with User

-- | Runs an interactive user session, loading the given exercise
-- This should be the main entry point for everything having to do with Agda.
runInteractiveSession :: Int -> FilePath -> IO ()
runInteractiveSession verbosity agdaFile = do
  ret <- initExercise verbosity agdaFile

  case ret of
    Left err -> printf "Exercise session failed with\n%s\n" err
    Right (exEnv, exState) -> do
      putStrLn $ unlines
        [ "Welcome to Martin - the interactive Agda tutor"
        , "You have loaded exercise " ++ show (view exerciseFile exEnv)
        , "Type `h` to get help!"
        , ""
        ]

      let go = do
            prettyProgram >>= outputStrLn
            outputStrLn ""
            exerciseLoop
      void $ runStateT (runReaderT (runInputT defaultSettings go) exEnv) exState

-- | The commands a user can perform at the top level interaction loop.
data TopCommand
  = CmdTopUndo       -- ^ undo the last split or refine action
  | CmdTopSelect Int -- ^ focus on a hole
  | CmdTopExit       -- ^ exit the program
  | CmdTopHelp       -- ^ print help message
  | CmdTopPrint      -- ^ print the program
  deriving (Eq, Ord, Show, Read)

-- | The commands a user can perform while being focused on a hole.
data HoleCommand
  = CmdHoleType      -- ^ print the hole type
  | CmdHoleContext   -- ^ print the hole context
  | CmdRefine String -- ^ refine the hole with the given expression
  | CmdSplit String  -- ^ split on the given variable
  | CmdHoleLeave     -- ^ leave the hole and return to the top level
  | CmdHoleHint      -- ^ print a hint for the hole
  deriving (Eq, Ord, Show, Read)

-- | Parser for TopCommands.
readPTopCommand :: ReadP.ReadP TopCommand
readPTopCommand = msum
  [ CmdTopUndo <$ ReadP.char 'u'
  , CmdTopExit <$ ReadP.char 'q'
  , CmdTopHelp <$ ReadP.char 'h'
  , CmdTopPrint <$ ReadP.char 'p'
  , CmdTopSelect <$> (ReadP.char 's' *> ReadP.skipSpaces *> ReadPrec.readPrec_to_P readPrec 0)
  ]

-- | Parser for HoleCommands.
readPHoleCommand :: ReadP.ReadP HoleCommand
readPHoleCommand = msum
  [ CmdHoleType <$ ReadP.char 't'
  , CmdHoleContext <$ ReadP.char 'c'
  , CmdHoleLeave <$ ReadP.char 'l'
  , CmdHoleHint <$ ReadP.char 'h'
  , CmdRefine <$> (ReadP.char 'r' *> ReadP.skipSpaces *> ReadP.many1 ReadP.get)
  , CmdSplit <$> (ReadP.char 's' *> ReadP.skipSpaces *> ReadP.many1 ReadP.get)
  ]

-- | Runs a parser.
runReadP :: ReadP.ReadP a -> String -> Maybe a
runReadP p s =
  case [ x | (x,"") <- ReadPrec.readPrec_to_S (ReadPrec.lift p) 0 s ] of
    [x] -> Just x
    _   -> Nothing

-- | The top level interaction loop.
exerciseLoop :: ExerciseM ()
exerciseLoop = do
  -- check if there are still holes to be filled
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
        exerciseHintLevel .= 0
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

-- | Catches prettified TCM errors in the InputT monad, and runs the continuation
-- from the error handler.
catchTCMErr :: MonadException m => InputT m a -> InputT m a -> InputT m a
catchTCMErr cont act = HaskEx.catch act $ \e -> do
  outputStrLn "Agda returned an error:\n"
  outputStrLn $ getPrettyTCErr e
  cont

-- | Interactive loop when focused on a hole.
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
      (doc, _) <- runTCMEx tcs $ B.typeOfMeta B.Normalised ii >>= \(B.OfType _ ty) -> A.prettyA ty
      outputStrLn $ render doc
      holeLoop ii
    Just CmdHoleContext -> do
      tcs <- use $ exerciseProgram . S.programTCState
      let prettyCtx (name, ty) = do
            let pname = pretty $ either id A.qnameName name
            pty <- A.prettyA ty
            return $ pname <+> char ':' <+> pty
      (doc, _) <- runTCMEx tcs $ AU.thingsInScopeWithType ii >>= mapM prettyCtx
      outputStrLn $ render $ vcat doc
      holeLoop ii
    Just (CmdSplit var) -> do
      splitUser ii var >>= mapM_ outputStrLn
      exerciseHintLevel .= 0
    Just (CmdRefine def) -> do
      refineUser ii def >>= mapM_ outputStrLn
      exerciseHintLevel .= 0
    Just CmdHoleHint -> do
      hint <- use exerciseHintLevel >>= giveHint ii
      exerciseHintLevel += 1
      mapM_ outputStrLn hint
      holeLoop ii

-- * Orphan instances

-- these orphan instances are required to make InputT work on top of our own monad transformer stack

instance MonadState s m => MonadState s (InputT m) where
  get = lift get
  put = lift . put

instance MonadReader e m => MonadReader e (InputT m) where
  ask = lift ask
  local f = mapInputT (local f)
