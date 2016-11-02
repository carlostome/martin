{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE OverloadedStrings #-}
-- | This module provides a simple dialog widget. You get to pick the
-- dialog title, if any, as well as its body and buttonList.
module Buttons
  ( -- * Button widget
    Button
  , button
  , buttonLabel
  , buttonValue
  , buttonShortcut
  , handleButtonEvent
    -- * Button list widget
  , ButtonList
  , buttonList
  , handleButtonListEvent
  , buttonListSelection
  , renderButtonList
  , activateButtons
    -- * Button attributes
  , buttonListAttr
  , buttonAttr
  , buttonSelectedAttr)
  where

import Control.Lens
import Data.Monoid
import Data.List (intersperse)
import Graphics.Vty.Input (Event(..), Key(..))

import Brick.Util (clamp)
import Brick.Types
import Brick.Widgets.Core
import Brick.Widgets.Center
import Brick.Widgets.Border
import Brick.AttrMap

data Button a = Button
  { _buttonLabel    :: String
  , _buttonValue    :: a
  , _buttonShortcut :: Maybe Char
  }
makeLenses ''Button

data ButtonList a = ButtonList
  { _buttonListButtons :: [Button a]
    -- ^ The dialog button labels and values
  , _buttonListSelectedIndex :: Maybe Int
    -- ^ The currently selected dialog button index (if any)
  }
makeLenses ''ButtonList

button :: String -> a -> Maybe Char -> Button a
button = Button

-- | Create a button list.
buttonList :: Int
           -- ^ The currently-selected button index (starting at zero)
           -> [Button a]
           -- ^ the button labels and values to use
           -> ButtonList a
buttonList startIdx buttonData =
  let idx
        | null buttonData = Nothing
        | otherwise = Just $ clamp 0 (length buttonData - 1) startIdx
  in ButtonList buttonData idx

handleButtonListEvent :: Event -> ButtonList a -> ButtonList a
handleButtonListEvent ev br = case ev of
  EvKey (KChar '\t') [] -> nextButtonBy 1 br
  EvKey KBackTab [] -> nextButtonBy (-1) br
  EvKey KRight [] -> nextButtonBy 1 br
  EvKey KLeft [] -> nextButtonBy (-1) br
  _ -> br

activateButtons :: Event -> ButtonList a -> Maybe a
activateButtons ev br = case ev of
  EvKey KEnter [] -> case br ^. buttonListSelectedIndex of
    Nothing -> Nothing
    Just i -> firstOf (buttonListButtons . element i . buttonValue) br
  EvKey (KChar ch) [] -> firstOf (buttonListButtons
                                  . traverse
                                  . filtered (views buttonShortcut (== Just ch))
                                  . buttonValue) br
  _ -> Nothing

handleButtonEvent :: Event -> Button a -> Maybe a
handleButtonEvent ev btn = case ev of
  EvKey (KChar ch) []
    | Just ch == btn ^. buttonShortcut -> Just $ btn ^. buttonValue
  EvKey KEnter [] -> Just $ btn ^. buttonValue
  _ -> Nothing

-- | The default attribute of the dialog
buttonListAttr :: AttrName
buttonListAttr = "buttonList"

-- | The default attribute for all dialog buttonList
buttonAttr :: AttrName
buttonAttr = "button"

-- | The attribute for the selected dialog button (extends 'dialogAttr')
buttonSelectedAttr :: AttrName
buttonSelectedAttr = buttonAttr <> "selected"

renderButton :: Bool -> Button a -> Widget n
renderButton focused btn =
  let att | focused   = buttonSelectedAttr
          | otherwise = buttonAttr
  in withAttr att $ str $ "  " <> view buttonLabel btn <> "  "

renderButtonList :: ButtonList a -> Widget n
renderButtonList d =
    let buttonPadding = str "   "
        mkButton (i, btn) = renderButton (Just i == d^.buttonListSelectedIndex) btn
        btns = hBox $ intersperse buttonPadding $
                         mkButton <$> (zip [0..] (d^.buttonListButtons))
    in withDefAttr buttonListAttr btns

nextButtonBy :: Int -> ButtonList a -> ButtonList a
nextButtonBy amt d =
    let numButtonList = length $ view buttonListButtons d
    in if numButtonList == 0 then d
       else case view buttonListSelectedIndex d of
           Nothing -> d & buttonListSelectedIndex .~ (Just 0)
           Just i -> d & buttonListSelectedIndex .~ (Just $ (i + amt) `mod` numButtonList)

buttonListSelection :: ButtonList a -> Maybe a
buttonListSelection d =
  case view buttonListSelectedIndex d of
    Nothing -> Nothing
    Just i -> Just $ ((d^.buttonListButtons) !! i)^.buttonValue
