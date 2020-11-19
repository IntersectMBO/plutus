module NewProject.Types where

import Prelude
import Analytics (class IsEvent, Event)
import Data.Lens (Lens')
import Data.Lens.Record (prop)
import Data.Maybe (Maybe(..))
import Data.Symbol (SProxy(..))
import Projects.Types (Lang)

data Action
  = ChangeProjectName String -- TODO: confirm that we dont want to change the project name and remove
  | CreateProject Lang

defaultEvent :: String -> Event
defaultEvent action = { category: Just "NewProject", action, label: Nothing, value: Nothing }

instance isEventAction :: IsEvent Action where
  toEvent (ChangeProjectName _) = Just $ defaultEvent "ChangeProjectName"
  toEvent (CreateProject lang) = Just { category: Just "NewProject", action: "CreateProject", label: Just (show lang), value: Nothing }

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
