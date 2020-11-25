module ConfirmUnsavedNavigation.Types where

import Analytics (class IsEvent)
import Data.Lens (Lens')
import Data.Lens.Record (prop)
import Data.Maybe (Maybe(..))
import Data.Symbol (SProxy(..))

data Action
  =
   SaveProject
  | DontSaveProject
  | Cancel

instance isEventAction :: IsEvent Action where
  toEvent _ = Nothing

-- TODO: change state
type State
  = { projectName :: String
    , error :: Maybe String
    }

emptyState :: State
emptyState = { projectName: "New Project", error: Nothing }

_projectName :: Lens' State String
_projectName = prop (SProxy :: SProxy "projectName")

_error :: Lens' State (Maybe String)
_error = prop (SProxy :: SProxy "error")
