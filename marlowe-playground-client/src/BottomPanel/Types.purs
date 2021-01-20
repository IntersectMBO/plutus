module BottomPanel.Types where

import Prelude
import Analytics (class IsEvent, Event)
import Analytics as A
import Data.Lens (Lens')
import Data.Lens.Record (prop)
import Data.Maybe (Maybe(..))
import Data.Symbol (SProxy(..))

-- This action is parameterized in the `panel` type so we can have type safety on the different panels
-- we have, and the panelAction, which is needed to allow the contents of the panel, to fire actions
-- on the parent. The `panel` type could eventually be refactored into just having a Map/Record, if we dont
-- care for it to be type safe, and the PanelAction could eventually be refactored to Variants/Run.
data Action panel panelAction
  = SetVisibility Boolean
  | ChangePanel panel
  | PanelAction panelAction

defaultEvent :: String -> Event
defaultEvent s = A.defaultEvent $ "BottomPanel." <> s

instance actionIsEvent :: (Show panel, IsEvent panelAction) => IsEvent (Action panel panelAction) where
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
