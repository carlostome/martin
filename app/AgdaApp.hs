{-# LANGUAGE TemplateHaskell #-}
module AgdaApp where

import qualified Martin.Interaction     as MI
import qualified AgdaStrategy        as AS
import qualified AgdaInteraction    as AI
import Agda.Syntax.Common
import           Control.Lens
import           Data.Monoid
import qualified Options.Applicative as OA
import           System.IO
import           Text.Printf
import Control.Monad.IO.Class

import Data.Monoid
import Control.Lens

import qualified Graphics.Vty as V
import qualified Brick.Main as M
import qualified Brick.Types as T
import Brick.Widgets.Core
  ( (<+>)
  , (<=>)
  , hLimit
  , vLimit
  , str
  , padTop
  , padBottom
  )
import qualified Brick.Widgets.Center as C
import qualified Brick.Widgets.Edit as E
import qualified Brick.Widgets.Border as B
import qualified Brick.Widgets.Dialog as D
import qualified Brick.AttrMap as A
import qualified Brick.Focus as F
import Brick.Util (on)

--------------------------------------------------------------------------------

data Name = Edit
          deriving (Ord, Show, Eq)

data St =
    St {
         _edit :: E.Editor String Name
       , _currentWindow :: Window
       , _exState       :: MI.ExerciseState
       , _exProg        :: String
       , _userDialog   :: String
       }

data Window = HelpW | MainW

makeLenses ''St

drawUI :: St -> [T.Widget Name]
drawUI st = [ui]
    where
      e1 = F.withFocusRing (F.focusRing [Edit]) E.renderEditor (st^.edit)

      ui =
        case st^.currentWindow of
          HelpW   -> (C.center $ str help) <=>
                     str " " <=>
                     str "Esc to go back."
          MainW -> (C.center $ padBottom T.Max $ str (view exProg st)) <=>
                     str " " <=>
                     B.hBorder
                     <=>
                     D.renderDialog topLevelDialog 
                     (vLimit 1 $ padTop T.Max $ str (view userDialog st))
                     <=>
                     str " " <=>
                     str "Esc to quit. h to go to the help page."

data TopCommand
  = CmdTopUndo       -- ^ undo the last split or refine action
  | CmdTopSelect Int -- ^ focus on a hole
  | CmdTopExit       -- ^ exit the program
  | CmdTopHelp       -- ^ print help message
  | CmdTopPrint      -- ^ print the program
  deriving (Eq, Ord, Show, Read)

topLevelDialog :: D.Dialog TopCommand
topLevelDialog =
  D.dialog Nothing (Just (0, [("Exit", CmdTopExit), ("Select hole",CmdTopSelect 0), ("Undo", CmdTopUndo)]))
  30

appEvent :: MI.ExerciseEnv -> St -> V.Event -> T.EventM Name (T.Next St)
appEvent exEnv st ev =
  case st^.currentWindow of
    HelpW ->
      let returnToMain = T.handleEventLensed st currentWindow (\_ _ -> return MainW) ev >>= M.continue
      in case ev of
           V.EvKey V.KEsc []        -> returnToMain
           V.EvKey (V.KChar 'q') [] -> returnToMain
           _ -> M.continue st
    MainW ->
      case ev of
        -- Either Esc or q exits the app.
        V.EvKey V.KEsc [] -> M.halt st
        V.EvKey (V.KChar 'q') [] -> M.halt st
        -- h leads us to the Help window.
        V.EvKey (V.KChar 'h') [] ->
          M.continue =<< T.handleEventLensed st currentWindow (\_ _ -> return HelpW) ev
        -- u Undo last command.
        V.EvKey (V.KChar 'u') [] -> do
          (oldProg, oldState) <- liftIO $ MI.runExerciseM exEnv (view exState st)
                                           (MI.undo >> MI.prettyProgram)
          M.continue (st & exState .~ oldState
                         & exProg  .~ oldProg)
        V.EvKey (V.KChar 's') [] -> do
          ((feedback,newProg),newState) <-
              liftIO $ MI.runExerciseM exEnv (view exState st)
                         ((,) <$> MI.splitUser (InteractionId 0) "x"
                              <*> MI.prettyProgram)
          M.continue (st & exState .~ newState
                         & exProg  .~ newProg
                         & userDialog .~ show feedback)

        _ -> M.continue =<< case F.focusGetCurrent (F.focusRing [Edit]) of
               Just Edit -> T.handleEventLensed st edit E.handleEditorEvent ev
               Nothing -> return st
appEvent _ st _ = M.continue st


mkInitialState :: MI.ExerciseState -> String -> St
mkInitialState exState p =
    St (E.editor Edit (str . unlines) Nothing "")
       MainW
       exState
       p
       ""

theMap :: A.AttrMap
theMap = A.attrMap V.defAttr
    [ (E.editAttr,                   V.white `on` V.blue)
    , (E.editFocusedAttr,            V.black `on` V.yellow)
    ]

appCursor :: St -> [T.CursorLocation Name] -> Maybe (T.CursorLocation Name)
appCursor _ _ = Nothing

mkTheApp :: MI.ExerciseEnv -> M.App St V.Event Name
mkTheApp env =
  M.App { M.appDraw          = drawUI
        , M.appChooseCursor  = appCursor
        , M.appHandleEvent   = appEvent env
        , M.appStartEvent    = return
        , M.appAttrMap       = const theMap
        , M.appLiftVtyEvent  = id
        }

runApp :: FilePath -> IO ()
runApp agdaFile = do
  i <- MI.initExercise 0 agdaFile
  case i of
    Left err -> putStrLn err
    Right (exEnv,exState) -> do
      prog <- fst <$> MI.runExerciseM exEnv exState MI.prettyProgram
      _ <- M.defaultMain (mkTheApp exEnv) (mkInitialState exState prog)
      return ()

help :: String
help = unlines
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

