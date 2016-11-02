{-# LANGUAGE TemplateHaskell #-}
module AgdaApp where

import qualified AgdaInteraction        as AI
import qualified AgdaStrategy           as AS
import qualified Martin.Agda.Util       as AU
import qualified Martin.Interaction     as MI

import           Agda.Syntax.Common

import           Control.Lens
import Control.Exception as E
import           Control.Monad.IO.Class
import           Data.Monoid
import qualified Options.Applicative    as OA
import           System.IO
import           Text.Printf
import Text.Read

import qualified Brick.AttrMap          as A
import qualified Brick.Focus            as F
import qualified Brick.Main             as M
import qualified Brick.Types            as T
import           Brick.Util             (on, bg)
import qualified Brick.Widgets.Border   as B
import qualified Brick.Widgets.Center   as C
import           Brick.Widgets.Core     (hLimit, padBottom, padTop, str, vLimit,
                                         (<+>), (<=>), emptyWidget, vBox)
import qualified Brick.Widgets.Dialog   as D
import qualified Brick.Widgets.Edit     as E
import qualified Graphics.Vty           as V
import Data.List (isPrefixOf)

--------------------------------------------------------------------------------

data Name = Edit
          deriving (Ord, Show, Eq)

data TopCommand
  = CmdTopUndo       -- ^ undo the last split or refine action
  | CmdTopSelect     -- ^ focus on a hole
  | CmdTopHelp       -- ^ print help message
  | CmdTopSolve      -- ^ solve the exercise for the user
  deriving (Eq, Ord, Show, Read)

-- | The commands a user can perform while being focused on a hole.
data HoleCommand
  = CmdHoleType      -- ^ print the hole type
  | CmdHoleContext   -- ^ print the hole context
  | CmdRefine        -- ^ refine the hole with the given expression
  | CmdSplit         -- ^ split on the given variable
  | CmdHoleHint      -- ^ print a hint for the hole
  | CmdHoleHelp      -- ^ print a hint for the hole
  deriving (Eq, Ord, Show, Read)

data St =
    St {
         _edit          :: E.Editor String Name
       , _focus         :: Focus
       , _exState       :: MI.ExerciseState
       , _exEnv         :: MI.ExerciseEnv
       , _exProg        :: String
       , _userDialog    :: String
       , _topDialog     :: D.Dialog TopCommand
       , _holeDialog    :: D.Dialog HoleCommand
       }

data Focus = TopLevel | HoleLevel InteractionId | UserInput Action | Done
  deriving (Eq, Show)

data Action = Select | Refine InteractionId | Split InteractionId
  deriving (Eq,Show)


makeLenses ''St

drawUI :: St -> [T.Widget Name]
drawUI st = [ui]
    where
      e1 = F.withFocusRing (F.focusRing [Edit]) E.renderEditor (st^.edit)

      ui = vBox
        [ C.hCenter  $ str ('\n':'\n' : view exProg st)
        , case st^.focus of
            UserInput ii -> str (replicate 5 '\n')
            TopLevel     -> D.renderDialog (st^.topDialog)  emptyWidget
            HoleLevel ii -> D.renderDialog (st^.holeDialog) (str $ "Hole " ++ show ii ++ "\n")
            Done         -> D.renderDialog doneDialog  emptyWidget
        , str " "
        , vLimit 1 $ e1
        , str " "
        , {-vLimit 6 $-} str (view userDialog st)
        , str " "
        , B.hBorder
        , str " "
        , case st^.focus of
               UserInput _ -> str "Esc to go back."
               TopLevel    -> str "q to quit the app."
               Done        -> str "q to quit the app."
               HoleLevel _ -> str "Esc to go back."]


holeLevelDialog :: D.Dialog HoleCommand
holeLevelDialog =
  D.dialog Nothing (Just (0, commands)) 90
    where commands =
            [("[H]elp" , CmdHoleHelp )
            ,("[T]ype" , CmdHoleType )
            ,("[C]ontext", CmdHoleContext)
            ,("[R]efine", CmdRefine)
            ,("[S]plit", CmdSplit)
            ,("H[i]nt", CmdHoleHint)]

doneDialog :: D.Dialog ()
doneDialog =
  D.dialog Nothing (Just (0, commands)) 90
    where commands = [("Congratulations! You finished the exercise.",())]

topLevelDialog :: D.Dialog TopCommand
topLevelDialog =
  D.dialog Nothing (Just (0, commands)) 70
    where commands = [("[H]elp", CmdTopHelp)
                     ,("[S]elect hole",CmdTopSelect)
                     ,("[U]ndo", CmdTopUndo)
                     ,("S[o]lution", CmdTopSolve)]

appEvent :: St -> V.Event -> T.EventM Name (T.Next St)
appEvent st ev =
  case st^.focus of
    UserInput a ->
      case ev of
        V.EvKey V.KEnter [] ->
          case a of
            Select -> do
              case readMaybe (head (E.getEditContents (st^.edit))) of
                Nothing ->
                  M.continue (st & edit .~ editor
                                 & userDialog .~ ("Hole must be a number!"))
                Just n  -> do
                    let ii = InteractionId n
                    (ips,newState) <- liftIO $ MI.runExerciseM (view exEnv st) (view exState st)
                                        MI.currentInteractionPoints
                    if ii `elem` ips
                       then M.continue (st & focus .~ HoleLevel ii
                                           & edit .~ editor
                                           & userDialog .~ ("Successfully selected hole " ++ show ii))
                       else M.continue (st & edit .~ editor
                                           & userDialog .~ ("Hole does not exists!" ))
            Refine ii -> do
              let input = head (E.getEditContents (st^.edit))
              r  <- liftIO $ E.try $ MI.runExerciseM (view exEnv st) (view exState st)
                          (MI.exerciseHintLevel .= 0 >>
                           (,) <$> MI.refineUser ii input
                               <*> MI.prettyProgram)
              case r of
                Right ((feedback,newProg),newState) -> do
                  (ips,_) <- liftIO $ MI.runExerciseM (view exEnv st) newState
                                        MI.currentInteractionPoints
                  if null ips
                     then M.continue (st & focus .~ Done
                                         & edit .~ editor
                                         & exProg .~ newProg
                                         & exState .~ newState
                                         & userDialog .~ unlines feedback)
                     else M.continue (st & focus .~ TopLevel
                                         & edit .~ editor
                                         & exProg .~ newProg
                                         & exState .~ newState
                                         & userDialog .~ unlines feedback)
                Left e ->
                  M.continue (st & focus .~ HoleLevel ii
                                 & edit .~ editor
                                 & userDialog .~ MI.getPrettyTCErr e)

            Split ii -> do
              let var = head (E.getEditContents (st^.edit))
              r <- liftIO $ E.try $ MI.runExerciseM (view exEnv st) (view exState st)
                          (MI.exerciseHintLevel .= 0 >>
                            (,) <$> MI.splitUser ii var
                                <*> MI.prettyProgram)
              case r of
                Right ((feedback,newProg),newState) -> do
                  (ips,_) <- liftIO $ MI.runExerciseM (view exEnv st) newState
                                        MI.currentInteractionPoints
                  if null ips
                     then M.continue (st & focus .~ Done
                                         & edit .~ editor
                                         & exProg .~ newProg
                                         & exState .~ newState
                                         & userDialog .~ unlines feedback)
                     else M.continue (st & focus .~ TopLevel
                                         & edit .~ editor
                                         & exProg .~ newProg
                                         & exState .~ newState
                                         & userDialog .~ unlines feedback)
                Left e ->
                  M.continue (st & focus .~ HoleLevel ii
                                 & edit .~ editor
                                 & userDialog .~ MI.getPrettyTCErr e)

        V.EvKey V.KEsc [] ->
          M.continue (st & focus .~ TopLevel
                         & userDialog .~ "")

        _ -> do
          newSt <- case F.focusGetCurrent (F.focusRing [Edit]) of
                     Just Edit -> T.handleEventLensed st edit E.handleEditorEvent ev
                     Nothing -> return st
          case newSt^.focus of
            (UserInput Select) -> do
                  let partialVar = head (E.getEditContents (newSt^.edit))
                  (ips,_) <- liftIO $ MI.runExerciseM (view exEnv st) (view exState st)
                                        MI.currentInteractionPoints
                  let holes = map (\(InteractionId ii) -> show ii) ips
                  case filter (isPrefixOf partialVar) holes of
                    []  -> M.continue newSt
                    [n] -> case readMaybe n of
                              Nothing ->
                                M.continue (st & edit .~ editor
                                               & userDialog .~ ("Hole must be a number!"))
                              Just n  -> do
                                let ii = InteractionId n
                                if ii `elem` ips
                                  then M.continue (st & focus .~ HoleLevel ii
                                                      & edit .~ editor
                                                      & userDialog .~ ("Successfully selected hole " ++ show ii))
                                  else M.continue (st & edit .~ editor
                                                      & userDialog .~ ("Hole does not exists!" ))
                    _   -> M.continue newSt
            _   -> M.continue newSt
    TopLevel ->
      case ev of
        V.EvKey V.KEnter [] -> do
          execTopCmd (D.dialogSelection (st^.topDialog)) st >>= M.continue
        V.EvKey (V.KChar 'q') [] -> M.halt st
        V.EvKey (V.KChar 'h') [] ->
          execTopCmd (Just CmdTopHelp) st >>= M.continue
        V.EvKey (V.KChar 's') [] ->
          execTopCmd (Just CmdTopSelect) st >>= M.continue
        V.EvKey (V.KChar 'u') [] ->
          execTopCmd (Just CmdTopUndo) st >>= M.continue
        V.EvKey (V.KChar 'o') [] ->
          execTopCmd (Just CmdTopSolve) st >>= M.continue
        _ -> do
          newDialog <- D.handleDialogEvent ev (st^.topDialog)
          M.continue (st & topDialog .~ newDialog)

    HoleLevel ii ->
      case ev of
        V.EvKey V.KEnter [] -> do
          execHoleCmd (D.dialogSelection (st^.holeDialog)) st >>= M.continue
        V.EvKey (V.KChar 'h') [] ->
          execHoleCmd (Just CmdHoleHelp) st >>= M.continue
        V.EvKey (V.KChar 't') [] ->
          execHoleCmd (Just CmdHoleType) st >>= M.continue
        V.EvKey (V.KChar 'c') [] ->
          execHoleCmd (Just CmdHoleContext) st >>= M.continue
        V.EvKey (V.KChar 'r') [] ->
          execHoleCmd (Just CmdRefine) st >>= M.continue
        V.EvKey (V.KChar 's') [] ->
          execHoleCmd (Just CmdSplit) st >>= M.continue
        V.EvKey (V.KChar 'i') [] ->
          execHoleCmd (Just CmdHoleHint) st >>= M.continue
        V.EvKey V.KEsc [] -> M.continue (st & focus .~ TopLevel
                                            & userDialog .~ "")
        _ -> do
          newDialog <- D.handleDialogEvent ev (st^.holeDialog)
          M.continue (st & holeDialog .~ newDialog)
    Done ->
      case ev of
        V.EvKey (V.KChar 'q') [] -> M.halt st
        _ -> M.continue st

execHoleCmd :: Maybe HoleCommand -> St -> T.EventM Name St
execHoleCmd Nothing st = return st
execHoleCmd (Just cmd) st = do
  let HoleLevel ii = st^.focus
  case cmd of
    CmdRefine -> return (st & focus .~ UserInput (Refine ii)
                            & userDialog .~ "Enter expression to refine")
    CmdSplit  ->
      return (st & focus .~ UserInput (Split ii)
                 & userDialog .~ "Enter variable to split")
    CmdHoleType   -> do
      (type',newState) <- liftIO $ MI.runExerciseM (view exEnv st) (view exState st)
                                 (MI.typeOfHole ii)
      return (st & exState .~ newState
                 & userDialog .~ type')
    CmdHoleContext  -> do
      (context,newState) <- liftIO $ MI.runExerciseM (view exEnv st) (view exState st)
                                 (MI.contextOfHole ii)
      return (st & exState .~ newState
                 & userDialog .~ (unlines context))
    CmdHoleHint  -> do
      (hint,newState) <- liftIO $ MI.runExerciseM (view exEnv st) (view exState st)
                          (use MI.exerciseHintLevel >>= MI.giveHint ii >>= \h -> MI.exerciseHintLevel += 1 >> return h)
      return (st & exState .~ newState
                 & userDialog .~ unlines hint)
    CmdHoleHelp   ->
      return $ st & userDialog .~ holeLevelhelp

execTopCmd :: Maybe TopCommand -> St -> T.EventM Name St
execTopCmd Nothing st = return st
execTopCmd (Just cmd) st =
  case cmd of
    CmdTopUndo -> do
      (oldProg, oldState) <- liftIO $ MI.runExerciseM (view exEnv st) (view exState st)
                                         (MI.undo >> (MI.exerciseHintLevel .= 0) >> MI.prettyProgram)
      return (st & exState .~ oldState
                 & exProg  .~ oldProg)
    CmdTopSelect -> do
      return (st & focus .~ UserInput Select
                 & userDialog .~ "Enter a hole number")
    CmdTopHelp   ->
      return $ st & userDialog .~ topLevelhelp
    CmdTopSolve -> do
      ((feedback, newProg, ips), exSt) <- liftIO $ MI.runExerciseM (view exEnv st) (view exState st) $
                                     (,,) <$> MI.solveExercise <*> MI.prettyProgram <*> MI.currentInteractionPoints
      return $ st & focus .~ (if null ips then Done else TopLevel)
                  & exState .~ exSt
                  & exProg .~ newProg
                  & userDialog .~ unlines feedback

editor = E.editor Edit (str . unlines) Nothing ""

mkInitialState :: MI.ExerciseEnv -> MI.ExerciseState -> String -> St
mkInitialState exEnv exState prog =
    St editor
       TopLevel
       exState
       exEnv
       prog
       ""
       topLevelDialog
       holeLevelDialog


theMap :: A.AttrMap
theMap = A.attrMap V.defAttr
    [ (D.dialogAttr, V.white `on` V.blue)
    , (D.buttonAttr, V.black `on` V.white)
    , (D.buttonSelectedAttr, bg V.yellow)
    , (E.editAttr, V.black `on` V.white)
    ]

appCursor :: St -> [T.CursorLocation Name] -> Maybe (T.CursorLocation Name)
appCursor _ _ = Nothing

theApp :: M.App St V.Event Name
theApp =
  M.App { M.appDraw          = drawUI
        , M.appChooseCursor  = appCursor
        , M.appHandleEvent   = appEvent
        , M.appStartEvent    = return
        , M.appAttrMap       = const theMap
        , M.appLiftVtyEvent  = id
        }

runApp :: AU.AgdaOptions -> FilePath -> IO ()
runApp agdaOpts agdaFile = do
  i <- MI.initExercise agdaOpts agdaFile
  case i of
    Left err -> putStrLn err
    Right (exEnv,exState) -> do
      prog <- fst <$> MI.runExerciseM exEnv exState MI.prettyProgram
      _ <- M.defaultMain theApp  (mkInitialState exEnv exState prog)
      return ()

topLevelhelp :: String
topLevelhelp = unlines
          [ "Welcome to martin, the interactive Agda tutor."
          , " "
          , "  We are now in the top level."
          , " "
          , "  You can either selected a hole to work on"
          , "  or undo your last step."
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
