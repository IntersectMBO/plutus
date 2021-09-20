module NewProject.Types where

import Prelude
import Analytics (class IsEvent)
import Data.Lens (Lens')
import Data.Lens.Record (prop)
import Data.Maybe (Maybe(..))
import Data.Symbol (SProxy(..))
import Projects.Types (Lang)

data Action
  = CreateProject Lang
  | Cancel

instance isEventAction :: IsEvent Action where
  toEvent (CreateProject lang) = Just { category: Just "NewProject", action: "CreateProject", label: Just (show lang), value: Nothing }
  toEvent Cancel = Just { category: Just "NewProject", action: "Cancel", label: Nothing, value: Nothing }

type State
  = { error :: Maybe String
    }

emptyState :: State
emptyState = { error: Nothing }

_error :: Lens' State (Maybe String)
_error = prop (SProxy :: SProxy "error")
