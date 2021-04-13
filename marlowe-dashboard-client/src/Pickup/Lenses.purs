module Pickup.Lenses (_pickupWalletString) where

import Data.Lens (Lens')
import Data.Lens.Record (prop)
import Data.Symbol (SProxy(..))
import Pickup.Types (State)

_pickupWalletString :: Lens' State String
_pickupWalletString = prop (SProxy :: SProxy "pickupWalletString")
