module Types where

import Prelude
import Chain.Types (ChainFocus)
import Chain.Types as Chain
import Data.Generic.Rep (class Generic)
import Data.Json.JsonUUID (JsonUUID)
import Data.Lens (Lens')
import Data.Lens.Iso.Newtype (_Newtype)
import Data.Lens.Record (prop)
import Data.Map (Map)
import Data.Maybe (Maybe)
import Data.Newtype (class Newtype)
import Data.RawJson (RawJson)
import Data.Symbol (SProxy(..))
import Network.RemoteData (RemoteData)
import Playground.Types (FunctionSchema)
import Plutus.SCB.Events.Contract (ContractInstanceId, ContractInstanceState, PartiallyDecodedResponse)
import Plutus.SCB.Types (ContractExe)
import Plutus.SCB.Webserver.Types (ContractSignatureResponse, FullReport, _FullReport)
import Schema.Types (SimulationAction)
import Servant.PureScript.Ajax (AjaxError)
import Wallet.Rollup.Types (AnnotatedTx)

data Query a

type WebData
  = RemoteData AjaxError

data HAction
  = Init
  | LoadFullReport
  | ChainAction (Maybe ChainFocus)
  | InvokeContractEndpoint SimulationAction

newtype State
  = State
  { fullReport :: WebData (FullReport ContractExe)
  , chainState :: Chain.State
  , contractSignatures :: Map ContractInstanceId (WebData (ContractSignatureResponse ContractExe))
  }

derive instance newtypeState :: Newtype State _

derive instance genericState :: Generic State _

_fullReport :: Lens' State (WebData (FullReport ContractExe))
_fullReport = _Newtype <<< prop (SProxy :: SProxy "fullReport")

_chainState :: Lens' State Chain.State
_chainState = _Newtype <<< prop (SProxy :: SProxy "chainState")

_contractSignatures :: Lens' State (Map ContractInstanceId (WebData (ContractSignatureResponse ContractExe)))
_contractSignatures = _Newtype <<< prop (SProxy :: SProxy "contractSignatures")

_annotatedBlockchain :: Lens' (FullReport ContractExe) (Array (Array AnnotatedTx))
_annotatedBlockchain = _FullReport <<< prop (SProxy :: SProxy "annotatedBlockchain")

_latestContractStatuses :: Lens' (FullReport ContractExe) (Array (ContractInstanceState ContractExe))
_latestContractStatuses = _FullReport <<< prop (SProxy :: SProxy "latestContractStatuses")

_csContract :: forall t. Lens' (ContractInstanceState t) ContractInstanceId
_csContract = _Newtype <<< prop (SProxy :: SProxy "csContract")

_csCurrentState :: forall t. Lens' (ContractInstanceState t) PartiallyDecodedResponse
_csCurrentState = _Newtype <<< prop (SProxy :: SProxy "csCurrentState")

_hooks :: Lens' PartiallyDecodedResponse RawJson
_hooks = _Newtype <<< prop (SProxy :: SProxy "hooks")

_contractInstanceId :: Lens' ContractInstanceId JsonUUID
_contractInstanceId = _Newtype <<< prop (SProxy :: SProxy "unContractInstanceId")
