module Pickup.Lenses
  ( _pickupWalletString
  , _pickingUp
  ) where

import Data.Lens (Lens')
import Data.Lens.Record (prop)
import Data.Symbol (SProxy(..))
import Pickup.Types (State)

_pickupWalletString :: Lens' State String
_pickupWalletString = prop (SProxy :: SProxy "pickupWalletString")

_pickingUp :: Lens' State Boolean
_pickingUp = prop (SProxy :: SProxy "pickingUp")
