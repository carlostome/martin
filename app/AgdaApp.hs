{-# LANGUAGE LambdaCase      #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE TemplateHaskell #-}
module AgdaApp where

import qualified Martin.Agda.Util           as AU
import qualified Martin.Interaction         as MI

import           Agda.Syntax.Common

import           Control.Exception          as E
import           Control.Lens
import           Control.Monad.IO.Class
import           Control.Monad.State.Strict
import           Control.Monad.Reader
import           Data.List                  (isPrefixOf)
import           Text.Printf
import           Text.Read (readMaybe)

import qualified Brick.AttrMap              as Brick
import qualified Brick.Main                 as Brick
import qualified Brick.Types                as Brick
import qualified Brick.Util                 as Brick
import qualified Brick.Widgets.Border       as Brick
import qualified Brick.Widgets.Center       as Brick
import qualified Brick.Widgets.Core         as Brick
import qualified Brick.Widgets.Edit         as Brick
import qualified Graphics.Vty               as Vty

import qualified Buttons                    as B

--------------------------------------------------------------------------------

data UIName = MiniBuffer | ProgramViewport
          deriving (Ord, Show, Eq)

data TopCommand
  = CmdTopUndo       -- ^ undo the last split or refine action
  | CmdTopSelect     -- ^ focus on a hole
  | CmdTopHelp       -- ^ print help message
  | CmdTopSolve      -- ^ solve the exercise for the user
  | CmdTopQuit       -- ^ quit the application
  deriving (Eq, Ord, Show, Read)

-- | The commands a user can perform while being focused on a hole.
data HoleCommand
  = CmdHoleType      -- ^ print the hole type
  | CmdHoleContext   -- ^ print the hole context
  | CmdRefine        -- ^ refine the hole with the given expression
  | CmdSplit         -- ^ split on the given variable
  | CmdHoleHint      -- ^ print a hint for the hole
  | CmdHoleHelp      -- ^ print a hint for the hole
  | CmdHoleLeave     -- ^ leave the hole
  deriving (Eq, Ord, Show, Read)

data UIMode = TopLevel | HoleLevel InteractionId | UserInput Action | Done
  deriving (Eq, Show)

data Action = Select | Refine InteractionId | Split InteractionId
  deriving (Eq,Show)


data UIState = UIState
  { _uiMiniBuffer :: Brick.Editor String UIName
  , _uiMode        :: UIMode
  , _uiProgramText :: String
  , _uiInfoText    :: String
  , _uiTopLevelBtn :: B.ButtonList TopCommand
  , _uiHoleBtn     :: B.ButtonList HoleCommand
  }

makeLenses ''UIState

data ExState = ExState
  { _exState :: MI.ExerciseState
  , _exEnv   :: MI.ExerciseEnv
  }

makeLenses ''ExState

data AppState = AppState
  { _appStateUI :: UIState
  , _appStateEx :: ExState
  }

makeLenses ''AppState

data StateNext s = Continue | Halt | RunIO (s -> IO s)
type StatefulHandler s n = StateT s (Brick.EventM n)

statefulHandler :: (e -> StatefulHandler s n (StateNext s)) -> s -> e -> Brick.EventM n (Brick.Next s)
statefulHandler f s e = runStateT (f e) s >>= \(nxt, s') ->
  case nxt of
    Continue -> Brick.continue s'
    Halt -> Brick.halt s'
    RunIO act -> Brick.suspendAndResume (act s')

type MartinHandler = StatefulHandler AppState UIName

drawUI :: UIState -> [Brick.Widget UIName]
drawUI st = [ui]
    where
      programView = Brick.hCenter $ Brick.border $
        Brick.viewport ProgramViewport Brick.Both $ Brick.str $ st ^. uiProgramText

      infoBox = let txt = st ^. uiInfoText
                in if null txt
                   then Brick.emptyWidget
                   else Brick.hCenter $ Brick.str txt

      miniBufferLabel a = case a of
        Select -> "Hole: "
        Refine _ -> "Expression: "
        Split _ -> "Variable: "

      interactionLine = Brick.border $ case st ^. uiMode of
        UserInput a  -> Brick.str (miniBufferLabel a) Brick.<+> Brick.renderEditor True (st ^. uiMiniBuffer)
        TopLevel     -> Brick.hCenter $ B.renderButtonList (st ^. uiTopLevelBtn)
        HoleLevel ii -> Brick.hCenter $ B.renderButtonList (st ^. uiHoleBtn)
        Done         -> Brick.hCenter $ Brick.str "Congratulations, you have solved the exercise! Press q to exit."

      ui = Brick.vBox
        [ programView
        , infoBox
        , interactionLine
        ]

-- * Event Handler

appEvent :: AppState -> Vty.Event -> Brick.EventM UIName (Brick.Next AppState)
appEvent = statefulHandler dispatch where
  dispatch evt = case evt of
    Vty.EvKey Vty.KUp [] -> do
      lift $ Brick.vScrollBy (Brick.viewportScroll ProgramViewport) (-1)
      return Continue
    Vty.EvKey Vty.KDown [] -> do
      lift $ Brick.vScrollBy (Brick.viewportScroll ProgramViewport) 1
      return Continue
    _ -> use (appStateUI . uiMode) >>= \case
      UserInput a  -> userInputEvent a evt >> return Continue
      TopLevel     -> topLevelEvent evt
      HoleLevel ii -> holeLevelEvent ii evt
      Done         -> doneEvent evt

userInputEvent :: Action -> Vty.Event -> MartinHandler ()
userInputEvent a ev = case ev of
  Vty.EvKey Vty.KEnter [] -> do
    text <- uses (appStateUI . uiMiniBuffer) (concat . Brick.getEditContents)
    miniBufferAction a text
  Vty.EvKey Vty.KEsc [] ->
    zoom appStateUI $ do
      uiMode .= case a of
        Select -> TopLevel
        Refine ii -> HoleLevel ii
        Split ii -> HoleLevel ii
      uiMiniBuffer .= miniBuffer
      uiInfoText .= ""
  _ -> do
    zoom (appStateUI . uiMiniBuffer) $ modifyM (lift . Brick.handleEditorEvent ev)
    text <- uses (appStateUI . uiMiniBuffer) (concat . Brick.getEditContents)
    miniBufferChanged a text

topLevelEvent :: Vty.Event -> MartinHandler (StateNext AppState)
topLevelEvent ev = do
  bl <- appStateUI . uiTopLevelBtn <%= B.handleButtonListEvent ev
  case B.activateButtons ev bl of
    Nothing -> return Continue
    Just cmd -> execTopCmd cmd

holeLevelEvent :: InteractionId -> Vty.Event -> MartinHandler (StateNext AppState)
holeLevelEvent ii ev = do
  bl <- appStateUI . uiHoleBtn <%= B.handleButtonListEvent ev
  Continue <$ forM_ (B.activateButtons ev bl) (execHoleCmd ii)

doneEvent :: Vty.Event -> MartinHandler (StateNext AppState)
doneEvent ev = case ev of
  Vty.EvKey (Vty.KChar 'q') [] -> return Halt
  _ -> return Continue

-- | Called when the user pressed enter in the mini buffer.
miniBufferAction :: Action -> String -> MartinHandler ()
miniBufferAction Select input = case readMaybe input of
  Nothing -> appStateUI . uiInfoText .= "Hole must be a number!"
  Just n -> do
    let ii = InteractionId n
    ips <- liftEx MI.currentInteractionPoints
    if ii `elem` ips
      then selectHole ii
      else appStateUI . uiInfoText .= printf "Hole does not exist!"
miniBufferAction (Refine ii) input = do
  r <- liftExCatch $ do
    MI.exerciseHintLevel .= 0
    MI.refineUser ii input
  case r of
    Left e ->
      appStateUI . uiInfoText .= MI.getPrettyTCErr e
    Right feedback -> finishUserAction feedback
miniBufferAction (Split ii) input = do
  r <- liftExCatch $ do
    MI.exerciseHintLevel .= 0
    MI.splitUser ii input
  case r of
    Left e ->
      appStateUI . uiInfoText .= MI.getPrettyTCErr e
    Right feedback -> finishUserAction feedback

finishUserAction :: MI.Feedback -> MartinHandler ()
finishUserAction feedback = do
  ips <- liftEx MI.currentInteractionPoints
  updateProgramText
  case ips of
    -- single hole left, directly select it
    [ii] -> selectHole ii
    _ -> zoom appStateUI $ do
      uiMode .= (if null ips then Done else TopLevel)
      uiInfoText .= unlines feedback
      uiMiniBuffer .= miniBuffer

miniBufferChanged :: Action -> String -> MartinHandler ()
miniBufferChanged Select input = do
  ips <- liftEx MI.currentInteractionPoints
  case filter (isPrefixOf input . show . interactionId) ips of
    [ii] -> selectHole ii
    _ -> return ()
miniBufferChanged (Split ii) input = do
  vars <- liftEx $ MI.localVariables ii
  case filter (isPrefixOf input) vars of
    [v] | v == input -> miniBufferAction (Split ii) v
    _ -> return ()
miniBufferChanged _ _ = return ()

selectHole :: InteractionId -> MartinHandler ()
selectHole ii = do
  appStateUI . uiMode .= HoleLevel ii
  appStateUI . uiInfoText .= printf "Selected hole %s!" (show ii)
  appStateUI . uiMiniBuffer .= miniBuffer

-- * Button commands

execTopCmd :: TopCommand -> MartinHandler (StateNext AppState)
execTopCmd CmdTopUndo = do
  success <- liftEx $ do
    MI.exerciseHintLevel .= 0
    MI.undo
  updateProgramText
  appStateUI . uiInfoText .= (if success then "Undone!" else "Nothing to undo!")
  return Continue
execTopCmd CmdTopSelect = do
  zoom appStateUI $ do
    uiMode .= UserInput Select
    uiInfoText .=  "Enter a hole number"
  return Continue
execTopCmd CmdTopHelp = do
  appStateUI . uiInfoText .= topLevelhelp
  return Continue
execTopCmd CmdTopSolve = do
  feedback <- liftEx MI.solveExercise
  appStateUI . uiInfoText .= unlines feedback
  return Continue
execTopCmd CmdTopQuit = return Halt

execHoleCmd :: InteractionId -> HoleCommand -> MartinHandler ()
execHoleCmd ii CmdRefine =
  zoom appStateUI $ do
    uiMode .= UserInput (Refine ii)
    uiInfoText .= "Enter expression to refine"
execHoleCmd ii CmdSplit =
  zoom appStateUI $ do
    uiMode .= UserInput (Split ii)
    uiInfoText .= "Enter variable to split"
execHoleCmd ii CmdHoleType = do
  ty <- liftEx $ MI.typeOfHole ii
  appStateUI . uiInfoText .= printf "Goal type: %s" ty
execHoleCmd ii CmdHoleContext = do
  context <- liftEx $ MI.contextOfHole ii
  appStateUI . uiInfoText .= printf "Context of hole:\n%s" (unlines context)
execHoleCmd ii CmdHoleHint = do
  hint <- liftEx $ do
    lvl <- MI.exerciseHintLevel <<+= 1
    MI.giveHint ii lvl
  appStateUI . uiInfoText .= unlines hint
execHoleCmd _ CmdHoleHelp =
  appStateUI . uiInfoText .= holeLevelhelp
execHoleCmd _ CmdHoleLeave = zoom appStateUI $ do
  uiMode .= TopLevel
  uiInfoText .= ""

-- * UI Update Functions

liftEx :: (MonadState AppState m, MonadIO m) => ReaderT MI.ExerciseEnv (StateT MI.ExerciseState IO) a -> m a
liftEx ex = do
  e <- use $ appStateEx . exEnv
  s <- use $ appStateEx . exState
  (a, s') <- liftIO $ MI.runExerciseM e s ex
  appStateEx . exState .= s'
  return a

liftExCatch :: (MonadState AppState m, MonadIO m) => ReaderT MI.ExerciseEnv (StateT MI.ExerciseState IO) a -> m (Either MI.PrettyTCErr a)
liftExCatch ex = do
  e <- use $ appStateEx . exEnv
  s <- use $ appStateEx . exState
  ret <- liftIO $ E.try $ MI.runExerciseM e s ex
  case ret of
    Left err -> return $ Left err
    Right (a, s') -> do
      appStateEx . exState .= s'
      return $ Right a

updateProgramText :: (MonadIO m) => StateT AppState m ()
updateProgramText = liftEx MI.prettyProgram >>= assign (appStateUI . uiProgramText)

-- * UI Component Definitions

miniBuffer :: Brick.Editor String UIName
miniBuffer = Brick.editor MiniBuffer (Brick.str . unlines) (Just 1) ""

holeLevelButtons :: B.ButtonList HoleCommand
holeLevelButtons = B.buttonList 0
  [B.button "[H]elp" CmdHoleHelp  (Just 'h')
  ,B.button "[T]ype" CmdHoleType  (Just 't')
  ,B.button "[C]ontext" CmdHoleContext (Just 'c')
  ,B.button "[R]efine" CmdRefine (Just 'r')
  ,B.button "[S]plit" CmdSplit (Just 's')
  ,B.button "H[i]nt" CmdHoleHint (Just 'i')
  ,B.button "[L]eave" CmdHoleLeave (Just 'l')
  ]

topLevelButtons :: B.ButtonList TopCommand
topLevelButtons = B.buttonList 0
  [B.button "[H]elp" CmdTopHelp (Just 'h')
  ,B.button "[S]elect hole" CmdTopSelect (Just 's')
  ,B.button "[U]ndo" CmdTopUndo (Just 'u')
  ,B.button "S[o]lution" CmdTopSolve (Just 'o')
  ,B.button "[Q]uit" CmdTopQuit (Just 'q')
  ]

topLevelhelp :: String
topLevelhelp = unlines
  [ "Welcome to martin, the interactive Agda tutor."
  , " "
  , "  We are now in the top level."
  , " "
  , "  You can either select a hole to work on or undo your last step."
  , "  If the program text doesn't fit your screen, you can use the up and down arrow keys to scroll."
  , " "
  ]

holeLevelhelp :: String
holeLevelhelp = unlines
  [ "Now that you select a hole you can:"
  , " "
  , "  Ask for the type of the hole."
  , "  Ask for items in the context of the hole."
  , "  Fill the hole with an expression."
  , "  Case split on a variable."
  , " "
  , "  If you are really stuck, you can ask me for a hint!"
  , "  (disclaimer: use this power wisely)"
  , " "
  ]

mkInitialState :: MI.ExerciseEnv -> MI.ExerciseState -> AppState
mkInitialState exEnv exState = AppState
  { _appStateUI = UIState
    { _uiMiniBuffer = miniBuffer
    , _uiMode        = TopLevel
    , _uiProgramText = ""
    , _uiInfoText    = ""
    , _uiTopLevelBtn = topLevelButtons
    , _uiHoleBtn     = holeLevelButtons
    }
  , _appStateEx = ExState exState exEnv
  }

attributes :: Brick.AttrMap
attributes = Brick.attrMap Vty.defAttr
  [ (B.buttonAttr, Vty.black `Brick.on` Vty.white)
  , (B.buttonSelectedAttr, Brick.bg Vty.yellow)
  , (Brick.editAttr, Vty.black `Brick.on` Vty.white)
  ]

appCursor :: s -> [Brick.CursorLocation n] -> Maybe (Brick.CursorLocation n)
appCursor _ _ = Nothing

-- * App Entry Point

theApp :: Brick.App AppState Vty.Event UIName
theApp = Brick.App
  { Brick.appDraw          = appStateUI `views` drawUI
  , Brick.appChooseCursor  = appCursor
  , Brick.appHandleEvent   = appEvent
  , Brick.appStartEvent    = return
  , Brick.appAttrMap       = const attributes
  , Brick.appLiftVtyEvent  = id
  }

runApp :: AU.AgdaOptions -> FilePath -> IO ()
runApp agdaOpts agdaFile = do
  i <- MI.initExercise agdaOpts agdaFile
  case i of
    Left err -> putStrLn err
    Right (exEnv,exState) -> do
      _ <- execStateT updateProgramText (mkInitialState exEnv exState) >>= Brick.defaultMain theApp
      return ()

-- * Helper functions

modifyM :: MonadState s m => (s -> m s) -> m ()
modifyM f = get >>= f >>= put
