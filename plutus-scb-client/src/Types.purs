module Types where

import Prelude
import Chain.Types (ChainFocus)
import Chain.Types as Chain
import Control.Monad.Gen as Gen
import Data.Generic.Rep (class Generic)
import Data.Generic.Rep.Show (genericShow)
import Data.Json.JsonMap (JsonMap)
import Data.Json.JsonUUID (JsonUUID, _JsonUUID)
import Data.Lens (Lens', Getter', to)
import Data.Lens.Iso.Newtype (_Newtype)
import Data.Lens.Record (prop)
import Data.Map (Map)
import Data.Maybe (Maybe)
import Data.Newtype (class Newtype)
import Data.NonEmpty ((:|))
import Data.Symbol (SProxy(..))
import Data.UUID as UUID
import Language.Plutus.Contract.Resumable (Request)
import Ledger.Index (UtxoIndex)
import Ledger.Tx (Tx)
import Ledger.TxId (TxId)
import Network.RemoteData (RemoteData)
import Playground.Types (FunctionSchema)
import Plutus.SCB.Events.Contract (ContractInstanceId, ContractInstanceState, PartiallyDecodedResponse, ContractSCBRequest)
import Plutus.SCB.Types (ContractExe)
import Plutus.SCB.Webserver.Types (ChainReport, ContractReport, FullReport, _ChainReport, _ContractReport)
import Schema (FormSchema)
import Schema.Types (FormArgument, FormEvent)
import Servant.PureScript.Ajax (AjaxError)
import Test.QuickCheck (class Arbitrary)
import Wallet.Rollup.Types (AnnotatedTx)

data Query a

type WebData
  = RemoteData AjaxError

data HAction
  = Init
  | ChangeView View
  | LoadFullReport
  | ChainAction (Maybe ChainFocus)
  | ChangeContractEndpointCall ContractInstanceId Int FormEvent
  | InvokeContractEndpoint ContractInstanceId EndpointForm

newtype State
  = State
  { currentView :: View
  , fullReport :: WebData (FullReport ContractExe)
  , chainState :: Chain.State
  , contractSignatures :: Map ContractInstanceId (WebData (Array EndpointForm))
  }

type EndpointForm
  = { schema :: FunctionSchema FormSchema
    , argument :: FormArgument
    }

derive instance newtypeState :: Newtype State _

derive instance genericState :: Generic State _

_currentView :: Lens' State View
_currentView = _Newtype <<< prop (SProxy :: SProxy "currentView")

_fullReport :: Lens' State (WebData (FullReport ContractExe))
_fullReport = _Newtype <<< prop (SProxy :: SProxy "fullReport")

_contractReport :: forall t. Lens' (FullReport t) (ContractReport t)
_contractReport = _Newtype <<< prop (SProxy :: SProxy "contractReport")

_chainReport :: forall t. Lens' (FullReport t) (ChainReport t)
_chainReport = _Newtype <<< prop (SProxy :: SProxy "chainReport")

_chainState :: Lens' State Chain.State
_chainState = _Newtype <<< prop (SProxy :: SProxy "chainState")

_contractSignatures :: Lens' State (Map ContractInstanceId (WebData (Array EndpointForm)))
_contractSignatures = _Newtype <<< prop (SProxy :: SProxy "contractSignatures")

_annotatedBlockchain :: forall t. Lens' (ChainReport t) (Array (Array AnnotatedTx))
_annotatedBlockchain = _ChainReport <<< prop (SProxy :: SProxy "annotatedBlockchain")

_transactionMap :: forall t. Lens' (ChainReport t) (JsonMap TxId Tx)
_transactionMap = _ChainReport <<< prop (SProxy :: SProxy "transactionMap")

_utxoIndex :: forall t. Lens' (ChainReport t) UtxoIndex
_utxoIndex = _ChainReport <<< prop (SProxy :: SProxy "utxoIndex")

_installedContracts :: forall t. Lens' (ContractReport t) (Array t)
_installedContracts = _ContractReport <<< prop (SProxy :: SProxy "installedContracts")

_latestContractStatuses :: forall t. Lens' (ContractReport t) (Array (ContractInstanceState t))
_latestContractStatuses = _ContractReport <<< prop (SProxy :: SProxy "latestContractStatuses")

_csContract :: forall t. Lens' (ContractInstanceState t) ContractInstanceId
_csContract = _Newtype <<< prop (SProxy :: SProxy "csContract")

_csCurrentState :: forall t. Lens' (ContractInstanceState t) (PartiallyDecodedResponse ContractSCBRequest)
_csCurrentState = _Newtype <<< prop (SProxy :: SProxy "csCurrentState")

_hooks :: forall t. Lens' (PartiallyDecodedResponse t) (Array (Request t))
_hooks = _Newtype <<< prop (SProxy :: SProxy "hooks")

_contractPath :: Lens' ContractExe String
_contractPath = _Newtype <<< prop (SProxy :: SProxy "contractPath")

_contractInstanceId :: Lens' ContractInstanceId JsonUUID
_contractInstanceId = _Newtype <<< prop (SProxy :: SProxy "unContractInstanceId")

_contractInstanceIdString :: Getter' ContractInstanceId String
_contractInstanceIdString = _contractInstanceId <<< _JsonUUID <<< to UUID.toString

------------------------------------------------------------
data View
  = ActiveContracts
  | Blockchain
  | EventLog

derive instance eqView :: Eq View

derive instance genericView :: Generic View _

instance arbitraryView :: Arbitrary View where
  arbitrary = Gen.elements (ActiveContracts :| [ Blockchain, EventLog ])

instance showView :: Show View where
  show = genericShow
