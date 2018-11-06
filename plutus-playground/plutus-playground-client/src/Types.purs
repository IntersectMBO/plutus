module Types where

import Ace.Halogen.Component (AceMessage)
import Data.Either (Either)
import Data.Lens (Lens')
import Data.Lens.Record (prop)
import Data.Newtype (class Newtype)
import Data.Symbol (SProxy(..))
import Halogen.ECharts (EChartsMessage)
import Network.RemoteData (RemoteData)
import Playground.API (FunctionsSchema)
import Playground.Interpreter (CompilationError)
import Servant.PureScript.Affjax (AjaxError)

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
  | CompileProgram a
  | SendAction Action a
  | KillAction Int a
  | AddWallet a
  | RemoveWallet Int a

-----------------------------------------------------------

type CompilationResult =
  Either (Array CompilationError) FunctionsSchema

type State =
  { wallets :: Array Wallet
  , actions :: Array Action
  , editorContents :: String
  , compilationResult :: RemoteData AjaxError CompilationResult
  }

_actions :: forall s a. Lens' {actions :: a | s} a
_actions = prop (SProxy :: SProxy "actions")

_wallets :: forall s a. Lens' {wallets :: a | s} a
_wallets = prop (SProxy :: SProxy "wallets")

_editorContents :: forall s a. Lens' {editorContents :: a | s} a
_editorContents = prop (SProxy :: SProxy "editorContents")

_compilationResult :: forall s a. Lens' {compilationResult :: a | s} a
_compilationResult = prop (SProxy :: SProxy "compilationResult")
