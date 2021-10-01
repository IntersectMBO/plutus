module Component.ConfirmUnsavedNavigation.Types where

import Prologue
import Analytics (class IsEvent, defaultEvent)

data Action
  = SaveProject
  | DontSaveProject
  | Cancel

instance isEventAction :: IsEvent Action where
  toEvent SaveProject = Just $ defaultEvent "ConfirmUnsavedNavigationSaveProject"
  toEvent DontSaveProject = Just $ defaultEvent "ConfirmUnsavedNavigationDontSaveProject"
  toEvent Cancel = Just $ defaultEvent "ConfirmUnsavedNavigationCancel"
