module BottomPanel.Types where

import Prelude
import Analytics (class IsEvent, Event)
import Analytics as A
import Data.Lens (Lens')
import Data.Lens.Record (prop)
import Data.Maybe (Maybe(..))
import Data.Symbol (SProxy(..))
import Marlowe.Extended (ContractType)
import Marlowe.Semantics as S

-- This component is an UI element that allows you to have different panels with titles at the bottom of the page. Because the children of this component is set by the page, the Action type
-- is parameterized in two types:
--   * The `panel` type defines the possible panels we can have inside this widget. Each page that uses this widget defines a type (normally called BottomPanelView) with the possible panels.
--     This type needs to implement Eq for the render function to show the current selected pane. By allowing this to be a sum type, we can get the type safety in the render functions that
--     we need to implement all possible panels. If we don't care about that, we could refactor to a Map/Record and lose this parameter.
--   * The `action` type allows the posibility for a panel to fire actions on the parent page by using the PanelAction constructor. I think it could be eventually be refactored as a Variant/Run.
data Action panel action
  = SetVisibility Boolean
  | ChangePanel panel
  | PanelAction action

defaultEvent :: String -> Event
defaultEvent s = A.defaultEvent $ "BottomPanel." <> s

instance actionIsEvent :: (Show panel, IsEvent action) => IsEvent (Action panel action) where
  toEvent (SetVisibility true) = Just $ defaultEvent "Show"
  toEvent (SetVisibility false) = Just $ defaultEvent "Hide"
  toEvent (ChangePanel view) = Just $ (defaultEvent "ChangePanel") { label = Just $ show view }
  toEvent (PanelAction action) = A.toEvent action

type State panel
  = { showBottomPanel :: Boolean
    , panelView :: panel
    }

initialState :: forall panel. panel -> State panel
initialState view =
  { showBottomPanel: false
  , panelView: view
  }

_showBottomPanel :: forall panel. Lens' (State panel) Boolean
_showBottomPanel = prop (SProxy :: SProxy "showBottomPanel")

_panelView :: forall panel. Lens' (State panel) panel
_panelView = prop (SProxy :: SProxy "panelView")

class ShowConstructor a where
  showConstructor :: a -> String

data MetadataAction
  = SetContractName String
  | SetContractType ContractType
  | SetContractDescription String
  | SetRoleDescription S.TokenName String
  | DeleteRoleDescription S.TokenName
  | SetSlotParameterDescription String String
  | DeleteSlotParameterDescription String
  | SetValueParameterDescription String String
  | DeleteValueParameterDescription String
  | SetChoiceDescription String String
  | DeleteChoiceDescription String

instance metadataActionShowConstructor :: ShowConstructor MetadataAction where
  showConstructor (SetContractName _) = "SetContractName"
  showConstructor (SetContractType _) = "SetContractType"
  showConstructor (SetContractDescription _) = "SetContractDescription"
  showConstructor (SetRoleDescription _ _) = "SetRoleDescription"
  showConstructor (DeleteRoleDescription _) = "DeleteRoleDescription"
  showConstructor (SetSlotParameterDescription _ _) = "SetSlotParameterDescription"
  showConstructor (DeleteSlotParameterDescription _) = "DeleteSlotParameterDescription"
  showConstructor (SetValueParameterDescription _ _) = "SetValueParameterDescription"
  showConstructor (DeleteValueParameterDescription _) = "DeleteValueParameterDescription"
  showConstructor (SetChoiceDescription _ _) = "SetChoiceDescription"
  showConstructor (DeleteChoiceDescription _) = "DeleteChoiceDescription"
