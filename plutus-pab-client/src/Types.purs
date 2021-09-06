module Types where

import Prelude
import Chain.Types as Chain
import Clipboard as Clipboard
import Control.Monad.Gen as Gen
import Data.Bifunctor (lmap)
import Data.Generic.Rep (class Generic)
import Data.Generic.Rep.Show (genericShow)
import Data.Json.JsonUUID (JsonUUID, _JsonUUID)
import Data.Json.JsonTuple (JsonTuple)
import Data.Lens (Getter', Iso', Traversal', Lens', to, traversed)
import Data.Lens.Iso.Newtype (_Newtype)
import Data.Lens.Record (prop)
import Data.Map (Map)
import Data.Maybe (Maybe(..))
import Data.Newtype (class Newtype)
import Data.NonEmpty ((:|))
import Data.Symbol (SProxy(..))
import Data.Tuple.Nested (type (/\))
import Data.UUID as UUID
import Foreign (MultipleErrors)
import Plutus.Contract.Resumable (Request)
import Ledger.Index (UtxoIndex)
import Plutus.V1.Ledger.Tx (Tx)
import Plutus.V1.Ledger.TxId (TxId)
import Network.RemoteData (RemoteData)
import Network.StreamData (StreamData)
import Network.StreamData as Stream
import Playground.Types (FunctionSchema)
import Plutus.Contract.Effects (PABReq, ActiveEndpoint, _ExposeEndpointReq)
import Plutus.PAB.Events.ContractInstanceState (PartiallyDecodedResponse)
import Plutus.PAB.Webserver.Types (ChainReport, ContractReport, ContractInstanceClientState, ContractSignatureResponse, _ChainReport, _ContractReport, _ContractInstanceClientState, _ContractSignatureResponse, CombinedWSStreamToClient, CombinedWSStreamToServer)
import Schema (FormSchema)
import Schema.Types (FormArgument, FormEvent)
import Servant.PureScript.Ajax (AjaxError)
import Test.QuickCheck (class Arbitrary)
import Wallet.Rollup.Types (AnnotatedTx)
import Wallet.Types (ContractInstanceId, EndpointDescription)
import Web.Socket.Event.CloseEvent (CloseEvent, reason) as WS
import WebSocket.Support (FromSocket) as WS
import ContractExample (ExampleContracts)

data Query a
  = ReceiveWebSocketMessage (WS.FromSocket CombinedWSStreamToClient) a

data Output
  = SendWebSocketMessage CombinedWSStreamToServer

data StreamError
  = DecodingError MultipleErrors
  | ServerError String
  | TransportError AjaxError

type WebStreamData
  = StreamData StreamError

type WebData
  = RemoteData AjaxError

fromWebData :: forall a. WebData a -> WebStreamData a
fromWebData = Stream.fromRemoteData <<< lmap TransportError

data HAction a
  = Init
  | ChangeView View
  | LoadFullReport
  | ActivateContract a
  | ChainAction Chain.Action
  | ClipboardAction Clipboard.Action
  | ChangeContractEndpointCall ContractInstanceId Int FormEvent
  | InvokeContractEndpoint ContractInstanceId EndpointForm

type ContractStates
  = Map ContractInstanceId (WebStreamData (ContractInstanceClientState ExampleContracts /\ Array EndpointForm))

newtype ContractSignatures a
  = ContractSignatures
  { unContractSignatures :: Array (ContractSignatureResponse a)
  }

derive instance genericContractSignatures :: Generic (ContractSignatures a) _

derive instance newtypeContractSignatures :: Newtype (ContractSignatures a) _

_ContractSignatures :: forall a. Iso' (ContractSignatures a) { unContractSignatures :: Array (ContractSignatureResponse a) }
_ContractSignatures = _Newtype

data WebSocketStatus
  = WebSocketOpen
  | WebSocketClosed (Maybe WS.CloseEvent)

derive instance genericWebSocketStatus :: Generic WebSocketStatus _

instance showWebSocketStatus :: Show WebSocketStatus where
  show WebSocketOpen = "WebSocketOpen"
  show (WebSocketClosed Nothing) = "WebSocketClosed"
  show (WebSocketClosed (Just closeEvent)) = "WebSocketClosed " <> WS.reason closeEvent

newtype State a
  = State
  { currentView :: View
  , contractSignatures :: WebStreamData (ContractSignatures a)
  , chainReport :: WebData ChainReport
  , chainState :: Chain.State
  , contractStates :: ContractStates
  , webSocketMessage :: WebStreamData CombinedWSStreamToClient
  , webSocketStatus :: WebSocketStatus
  }

type EndpointForm
  = { schema :: FunctionSchema FormSchema
    , argument :: FormArgument
    }

derive instance newtypeState :: Newtype (State a) _

derive instance genericState :: Generic (State a) _

_currentView :: forall a. Lens' (State a) View
_currentView = _Newtype <<< prop (SProxy :: SProxy "currentView")

_contractSignatures :: forall s r a. Newtype s { contractSignatures :: a | r } => Lens' s a
_contractSignatures = _Newtype <<< prop (SProxy :: SProxy "contractSignatures")

_chainReport :: forall s r a. Newtype s { chainReport :: a | r } => Lens' s a
_chainReport = _Newtype <<< prop (SProxy :: SProxy "chainReport")

_events :: forall s r a. Newtype s { events :: a | r } => Lens' s a
_events = _Newtype <<< prop (SProxy :: SProxy "events")

_chainState :: forall a. Lens' (State a) Chain.State
_chainState = _Newtype <<< prop (SProxy :: SProxy "chainState")

_contractStates :: forall a. Lens' (State a) ContractStates
_contractStates = _Newtype <<< prop (SProxy :: SProxy "contractStates")

_annotatedBlockchain :: Lens' ChainReport (Array (Array AnnotatedTx))
_annotatedBlockchain = _ChainReport <<< prop (SProxy :: SProxy "annotatedBlockchain")

_transactionMap :: Lens' ChainReport (Map TxId Tx)
_transactionMap = _ChainReport <<< prop (SProxy :: SProxy "transactionMap")

_webSocketMessage :: forall s a r. Newtype s { webSocketMessage :: a | r } => Lens' s a
_webSocketMessage = _Newtype <<< prop (SProxy :: SProxy "webSocketMessage")

_webSocketStatus :: forall s a r. Newtype s { webSocketStatus :: a | r } => Lens' s a
_webSocketStatus = _Newtype <<< prop (SProxy :: SProxy "webSocketStatus")

_contractReport :: forall s a r. Newtype s { contractReport :: a | r } => Lens' s a
_contractReport = _Newtype <<< prop (SProxy :: SProxy "contractReport")

_utxoIndex :: Lens' ChainReport UtxoIndex
_utxoIndex = _ChainReport <<< prop (SProxy :: SProxy "utxoIndex")

_crAvailableContracts :: forall t. Lens' (ContractReport t) (Array (ContractSignatureResponse t))
_crAvailableContracts = _ContractReport <<< prop (SProxy :: SProxy "crAvailableContracts")

_crActiveContractStates :: forall t. Lens' (ContractReport t) (Array (JsonTuple ContractInstanceId (PartiallyDecodedResponse PABReq)))
_crActiveContractStates = _ContractReport <<< prop (SProxy :: SProxy "crActiveContractStates")

_csrDefinition :: forall t. Lens' (ContractSignatureResponse t) t
_csrDefinition = _ContractSignatureResponse <<< prop (SProxy :: SProxy "csrDefinition")

_unContractSignatures :: forall t. Lens' (ContractSignatures t) (Array (ContractSignatureResponse t))
_unContractSignatures = _ContractSignatures <<< prop (SProxy :: SProxy "unContractSignatures")

_csContract :: forall t. Lens' (ContractInstanceClientState t) ContractInstanceId
_csContract = _Newtype <<< prop (SProxy :: SProxy "cicContract")

_csCurrentState :: forall t. Lens' (ContractInstanceClientState t) (PartiallyDecodedResponse ActiveEndpoint)
_csCurrentState = _Newtype <<< prop (SProxy :: SProxy "cicCurrentState")

_csContractDefinition :: forall t. Lens' (ContractInstanceClientState t) t
_csContractDefinition = _ContractInstanceClientState <<< prop (SProxy :: SProxy "cicDefinition")

_hooks :: forall t. Lens' (PartiallyDecodedResponse t) (Array (Request t))
_hooks = _Newtype <<< prop (SProxy :: SProxy "hooks")

_activeEndpoint :: Lens' ActiveEndpoint EndpointDescription
_activeEndpoint = _Newtype <<< prop (SProxy :: SProxy "aeDescription")

_contractActiveEndpoints :: Traversal' (PartiallyDecodedResponse ActiveEndpoint) EndpointDescription
_contractActiveEndpoints =
  _hooks
    <<< traversed
    <<< _rqRequest
    <<< _activeEndpoint

_rqRequest :: forall t. Lens' (Request t) t
_rqRequest = _Newtype <<< prop (SProxy :: SProxy "rqRequest")

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

------------------------------------------------------------
_getPubKeyHash :: forall s r a. Newtype s { getPubKeyHash :: a | r } => Lens' s a
_getPubKeyHash = _Newtype <<< prop (SProxy :: SProxy "getPubKeyHash")

propertyName _ = Nothing
