module Types where

import Data.Lens (Lens')
import Data.Lens.Record (prop)
import Data.Newtype (class Newtype)
import Data.Symbol (SProxy(..))

newtype WalletId = WalletId String
derive instance newtypeWalletId :: Newtype WalletId _

type Wallet =
  { walletId :: WalletId
  , balance :: Number
  }

_walletId :: forall s a. Lens' {walletId :: a | s} a
_walletId = prop (SProxy :: SProxy "walletId")

_balance :: forall s a. Lens' {balance :: a | s} a
_balance = prop (SProxy :: SProxy "balance")

------------------------------------------------------------

newtype ActionId = ActionId String
derive instance newtypeActionId :: Newtype ActionId _

_actionId :: forall s a. Lens' {actionId :: a | s} a
_actionId = prop (SProxy :: SProxy "actionId")

type Action =
  { actionId :: ActionId
  , walletId :: WalletId
  }
