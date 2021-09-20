module ConfirmUnsavedNavigation.Types where

import Prelude
import Analytics (class IsEvent, defaultEvent)
import Data.Maybe (Maybe(..))

data Action
  = SaveProject
  | DontSaveProject
  | Cancel

instance isEventAction :: IsEvent Action where
  toEvent SaveProject = Just $ defaultEvent "ConfirmUnsavedNavigationSaveProject"
  toEvent DontSaveProject = Just $ defaultEvent "ConfirmUnsavedNavigationDontSaveProject"
  toEvent Cancel = Just $ defaultEvent "ConfirmUnsavedNavigationCancel"
