module BottomPanel.State
  ( handleAction
  ) where

import Prelude hiding (div)
import BottomPanel.Types (Action(..), State, _panelView, _showBottomPanel)
import Data.Lens (assign, set)
import Halogen (HalogenM, modify_)
import MainFrame.Types (ChildSlots)

handleAction ::
  forall m panel action.
  Action panel action ->
  HalogenM (State panel) (Action panel action) ChildSlots Void m Unit
handleAction (SetVisibility val) = assign _showBottomPanel val

handleAction (ChangePanel view) =
  modify_
    (set _panelView view <<< set _showBottomPanel true)

handleAction (PanelAction _) = pure unit
