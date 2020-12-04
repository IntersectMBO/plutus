module ConfirmUnsavedNavigation.Types where

import Analytics (class IsEvent, defaultEvent)
import Data.Maybe (Maybe(..))
import Prelude (($))

data Action
  = SaveProject
  | DontSaveProject
  | Cancel

instance isEventAction :: IsEvent Action where
  toEvent SaveProject = Just $ defaultEvent "ConfirmUnsavedNavigationSaveProject"
  toEvent DontSaveProject = Just $ defaultEvent "ConfirmUnsavedNavigationDontSaveProject"
  toEvent Cancel = Just $ defaultEvent "ConfirmUnsavedNavigationCancel"
