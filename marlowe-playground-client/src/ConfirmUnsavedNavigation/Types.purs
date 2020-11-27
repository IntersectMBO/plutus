module ConfirmUnsavedNavigation.Types where

import Analytics (class IsEvent)
import Data.Lens (Lens')
import Data.Lens.Record (prop)
import Data.Maybe (Maybe(..))
import Data.Symbol (SProxy(..))

data Action
  = SaveProject
  | DontSaveProject
  | Cancel

instance isEventAction :: IsEvent Action where
  toEvent _ = Nothing

type State
  = { wantsToSaveProject :: Boolean
    }

emptyState :: State
emptyState = { wantsToSaveProject: true }

-- FIXME, dont quite like the name :/
_wantsToSaveProject :: Lens' State Boolean
_wantsToSaveProject = prop (SProxy :: SProxy "wantsToSaveProject")
