module Types where

import Data.Lens (Lens')
import Data.Lens.Record (prop)
import Ace.Halogen.Component (AceMessage)
import Halogen.ECharts (EChartsMessage)
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

------------------------------------------------------------

data Query a
  = HandleAceMessage AceMessage a
  | HandleEChartsMessage EChartsMessage a
  | SendAction Action a
  | KillAction Int a

-----------------------------------------------------------

type State =
  { wallets :: Array Wallet
  , actions :: Array Action
  }

_actions :: forall s a. Lens' {actions :: a | s} a
_actions = prop (SProxy :: SProxy "actions")

_wallets :: forall s a. Lens' {wallets :: a | s} a
_wallets = prop (SProxy :: SProxy "wallets")
