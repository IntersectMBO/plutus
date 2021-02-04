module MainFrame.Lenses
  ( _overlay
  , _screen
  , _card
  , _on
  ) where

import Data.Maybe (Maybe)
import Data.Lens (Lens')
import Data.Lens.Record (prop)
import Data.Symbol (SProxy(..))
import MainFrame.Types (Card, Contract, ContractTemplate, Notification, Screen, State, Overlay)

_overlay :: Lens' State (Maybe Overlay)
_overlay = prop (SProxy :: SProxy "overlay")

_screen :: Lens' State Screen
_screen = prop (SProxy :: SProxy "screen")

_card :: Lens' State (Maybe Card)
_card = prop (SProxy :: SProxy "card")

_notifications :: Lens' State (Array Notification)
_notifications = prop (SProxy :: SProxy "notifications")

_contractTemplates :: Lens' State (Array ContractTemplate)
_contractTemplates = prop (SProxy :: SProxy "contractTemplates")

_runningContracts :: Lens' State (Array Contract)
_runningContracts = prop (SProxy :: SProxy "runningContracts")

_on :: Lens' State Boolean
_on = prop (SProxy :: SProxy "on")
