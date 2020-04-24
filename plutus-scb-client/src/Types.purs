module Types where

import Prelude

import Chain.Types (ChainFocus)
import Chain.Types as Chain
import Data.Generic.Rep (class Generic)
import Data.Lens (Lens')
import Data.Lens.Iso.Newtype (_Newtype)
import Data.Lens.Record (prop)
import Data.Maybe (Maybe)
import Data.Newtype (class Newtype)
import Data.RawJson (RawJson)
import Data.Symbol (SProxy(..))
import Network.RemoteData (RemoteData)
import Plutus.SCB.Types (ActiveContractState, ContractExe, PartiallyDecodedResponse)
import Plutus.SCB.Webserver.Types (FullReport, _FullReport)
import Servant.PureScript.Ajax (AjaxError)
import Wallet.Rollup.Types (AnnotatedTx)

data Query a

type WebData
  = RemoteData AjaxError

data HAction
  = Init
  | LoadFullReport
  | ChainAction (Maybe ChainFocus)

newtype State
  = State
  { fullReport :: WebData (FullReport ContractExe)
  , chainState :: Chain.State
  }

derive instance newtypeState :: Newtype State _

derive instance genericState :: Generic State _

_fullReport :: Lens' State (WebData (FullReport ContractExe))
_fullReport = _Newtype <<< prop (SProxy :: SProxy "fullReport")

_chainState :: Lens' State Chain.State
_chainState = _Newtype <<< prop (SProxy :: SProxy "chainState")

_annotatedBlockchain :: Lens' (FullReport ContractExe) (Array (Array AnnotatedTx))
_annotatedBlockchain = _FullReport <<< prop (SProxy :: SProxy "annotatedBlockchain")

_partiallyDecodedResponse :: forall t. Lens' (ActiveContractState t) PartiallyDecodedResponse
_partiallyDecodedResponse = _Newtype <<< prop (SProxy :: SProxy "partiallyDecodedResponse")

_hooks :: Lens' PartiallyDecodedResponse RawJson
_hooks = _Newtype <<< prop (SProxy :: SProxy "hooks")
