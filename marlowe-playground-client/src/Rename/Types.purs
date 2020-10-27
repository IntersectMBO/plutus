module Rename.Types where

import Analytics (class IsEvent)
import Data.Lens (Lens')
import Data.Lens.Record (prop)
import Data.Maybe (Maybe(..))
import Data.Symbol (SProxy(..))

data Action
  = ChangeInput String
  | SaveProject

instance isEventAction :: IsEvent Action where
  toEvent (ChangeInput _) = Nothing
  toEvent SaveProject = Just { category: Just "Rename", action: "SaveProject", label: Nothing, value: Nothing }

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
