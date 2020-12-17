module SaveAs.Types where

import Prelude (Void)
import Analytics (class IsEvent)
import Data.Lens (Lens')
import Data.Lens.Record (prop)
import Data.Maybe (Maybe(..))
import Data.Symbol (SProxy(..))
import Network.RemoteData (RemoteData(..))

data Action
  = ChangeInput String
  | SaveProject
  | Cancel

instance isEventAction :: IsEvent Action where
  toEvent (ChangeInput _) = Nothing
  toEvent SaveProject = Just { category: Just "SaveAs", action: "SaveProject", label: Nothing, value: Nothing }
  toEvent Cancel = Just { category: Just "SaveAs", action: "Cancel", label: Nothing, value: Nothing }

type State
  = { projectName :: String
    -- We need a data type that handles NotAsked, Error and Loading to store the current status of the modal.
    -- Rather than creating a new data type I prefer to reuse RemoteData using Void as the successful response
    -- indicating that we don't care / use it.
    , status :: RemoteData String Void
    }

emptyState :: State
emptyState = { projectName: "New Project", status: NotAsked }

_projectName :: Lens' State String
_projectName = prop (SProxy :: SProxy "projectName")

_status :: Lens' State (RemoteData String Void)
_status = prop (SProxy :: SProxy "status")
