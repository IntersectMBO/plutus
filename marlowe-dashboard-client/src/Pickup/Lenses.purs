module Pickup.Lenses
  ( _card
  , _walletLibrary
  , _pickupWalletString
  , _walletDetails
  , _pickingUp
  ) where

import Data.Lens (Lens')
import Data.Lens.Record (prop)
import Data.Maybe (Maybe)
import Data.Symbol (SProxy(..))
import Pickup.Types (Card, State)
import WalletData.Types (WalletDetails, WalletLibrary)

_card :: Lens' State (Maybe Card)
_card = prop (SProxy :: SProxy "card")

_walletLibrary :: Lens' State WalletLibrary
_walletLibrary = prop (SProxy :: SProxy "walletLibrary")

_pickupWalletString :: Lens' State String
_pickupWalletString = prop (SProxy :: SProxy "pickupWalletString")

_walletDetails :: Lens' State WalletDetails
_walletDetails = prop (SProxy :: SProxy "walletDetails")

_pickingUp :: Lens' State Boolean
_pickingUp = prop (SProxy :: SProxy "pickingUp")
