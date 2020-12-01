module ConfirmUnsavedNavigation.Types where

import Analytics (class IsEvent)
import Data.Maybe (Maybe(..))

data Action
  = SaveProject
  | DontSaveProject
  | Cancel

instance isEventAction :: IsEvent Action where
  toEvent _ = Nothing
