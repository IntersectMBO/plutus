module SimulationPage.Lenses where

import BottomPanel.Types as BottomPanel
import Data.Lens (Lens')
import Data.Lens.Record (prop)
import Data.Symbol (SProxy(..))
import Help (HelpContext)
import SimulationPage.Types (State, BottomPanelView)

_showRightPanel :: Lens' State Boolean
_showRightPanel = prop (SProxy :: SProxy "showRightPanel")

_helpContext :: Lens' State HelpContext
_helpContext = prop (SProxy :: SProxy "helpContext")

_bottomPanelState :: Lens' State (BottomPanel.State BottomPanelView)
_bottomPanelState = prop (SProxy :: SProxy "bottomPanelState")

_decorationIds :: Lens' State (Array String)
_decorationIds = prop (SProxy :: SProxy "decorationIds")
