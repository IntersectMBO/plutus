module Types where

import Language.Plutus.Contract.Effects.ExposeEndpoint (ActiveEndpoint)
import Prelude
import Cardano.Metadata.Types (PropertyDescription(..), PropertyKey(..))
import Cardano.Metadata.Types as Metadata
import Chain.Types as Chain
import Clipboard as Clipboard
import Control.Monad.Gen as Gen
import Data.Bifunctor (lmap)
import Data.Generic.Rep (class Generic)
import Data.Generic.Rep.Show (genericShow)
import Data.Json.JsonUUID (JsonUUID, _JsonUUID)
import Data.Lens (Getter', Traversal', Lens', to, traversed)
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
import Language.Plutus.Contract.Resumable (Request)
import Ledger.Index (UtxoIndex)
import Ledger.Tx (Tx)
import Ledger.TxId (TxId)
import Network.RemoteData (RemoteData)
import Network.StreamData (StreamData)
import Network.StreamData as Stream
import Playground.Types (FunctionSchema)
import Plutus.SCB.Events (ChainEvent)
import Plutus.SCB.Events.Contract (ContractInstanceState, ContractSCBRequest, PartiallyDecodedResponse, _ContractInstanceState, _UserEndpointRequest)
import Plutus.SCB.Types (ContractExe)
import Plutus.SCB.Webserver.Types (ChainReport, ContractReport, ContractSignatureResponse, StreamToClient, StreamToServer, _ChainReport, _ContractReport, _ContractSignatureResponse)
import Schema (FormSchema)
import Schema.Types (FormArgument, FormEvent)
import Servant.PureScript.Ajax (AjaxError)
import Test.QuickCheck (class Arbitrary)
import Wallet.Rollup.Types (AnnotatedTx)
import Wallet.Types (ContractInstanceId, EndpointDescription)
import Web.Socket.Event.CloseEvent (CloseEvent, reason) as WS
import WebSocket.Support (FromSocket) as WS

data Query a
  = ReceiveWebSocketMessage (WS.FromSocket StreamToClient) a

data Output
  = SendWebSocketMessage StreamToServer

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

data HAction
  = Init
  | ChangeView View
  | LoadFullReport
  | ActivateContract ContractExe
  | ChainAction Chain.Action
  | ClipboardAction Clipboard.Action
  | ChangeContractEndpointCall ContractInstanceId Int FormEvent
  | InvokeContractEndpoint ContractInstanceId EndpointForm

type ContractStates
  = Map ContractInstanceId (WebStreamData (ContractInstanceState ContractExe /\ Array EndpointForm))

type ContractSignatures
  = Array (ContractSignatureResponse ContractExe)

data WebSocketStatus
  = WebSocketOpen
  | WebSocketClosed (Maybe WS.CloseEvent)

derive instance genericWebSocketStatus :: Generic WebSocketStatus _

instance showWebSocketStatus :: Show WebSocketStatus where
  show WebSocketOpen = "WebSocketOpen"
  show (WebSocketClosed Nothing) = "WebSocketClosed"
  show (WebSocketClosed (Just closeEvent)) = "WebSocketClosed " <> WS.reason closeEvent

newtype State
  = State
  { currentView :: View
  , contractSignatures :: WebStreamData ContractSignatures
  , chainReport :: WebData ChainReport
  , events :: WebData (Array (ChainEvent ContractExe))
  , chainState :: Chain.State
  , contractStates :: ContractStates
  , webSocketMessage :: WebStreamData StreamToClient
  , webSocketStatus :: WebSocketStatus
  , metadata :: Map Metadata.Subject (Map PropertyKey PropertyDescription)
  }

type EndpointForm
  = { schema :: FunctionSchema FormSchema
    , argument :: FormArgument
    }

derive instance newtypeState :: Newtype State _

derive instance genericState :: Generic State _

_currentView :: Lens' State View
_currentView = _Newtype <<< prop (SProxy :: SProxy "currentView")

_contractSignatures :: forall s r a. Newtype s { contractSignatures :: a | r } => Lens' s a
_contractSignatures = _Newtype <<< prop (SProxy :: SProxy "contractSignatures")

_chainReport :: forall s r a. Newtype s { chainReport :: a | r } => Lens' s a
_chainReport = _Newtype <<< prop (SProxy :: SProxy "chainReport")

_events :: forall s r a. Newtype s { events :: a | r } => Lens' s a
_events = _Newtype <<< prop (SProxy :: SProxy "events")

_chainState :: Lens' State Chain.State
_chainState = _Newtype <<< prop (SProxy :: SProxy "chainState")

_contractStates :: Lens' State ContractStates
_contractStates = _Newtype <<< prop (SProxy :: SProxy "contractStates")

_metadata ::
  Lens' State
    ( Map Metadata.Subject (Map PropertyKey PropertyDescription)
    )
_metadata = _Newtype <<< prop (SProxy :: SProxy "metadata")

_annotatedBlockchain :: forall t. Lens' ChainReport (Array (Array AnnotatedTx))
_annotatedBlockchain = _ChainReport <<< prop (SProxy :: SProxy "annotatedBlockchain")

_transactionMap :: forall t. Lens' ChainReport (Map TxId Tx)
_transactionMap = _ChainReport <<< prop (SProxy :: SProxy "transactionMap")

_webSocketMessage :: forall s a r. Newtype s { webSocketMessage :: a | r } => Lens' s a
_webSocketMessage = _Newtype <<< prop (SProxy :: SProxy "webSocketMessage")

_webSocketStatus :: forall s a r. Newtype s { webSocketStatus :: a | r } => Lens' s a
_webSocketStatus = _Newtype <<< prop (SProxy :: SProxy "webSocketStatus")

_contractReport :: forall s a r. Newtype s { contractReport :: a | r } => Lens' s a
_contractReport = _Newtype <<< prop (SProxy :: SProxy "contractReport")

_utxoIndex :: forall t. Lens' ChainReport UtxoIndex
_utxoIndex = _ChainReport <<< prop (SProxy :: SProxy "utxoIndex")

_crAvailableContracts :: forall t. Lens' (ContractReport t) (Array (ContractSignatureResponse t))
_crAvailableContracts = _ContractReport <<< prop (SProxy :: SProxy "crAvailableContracts")

_crActiveContractStates :: forall t. Lens' (ContractReport t) (Array (ContractInstanceState t))
_crActiveContractStates = _ContractReport <<< prop (SProxy :: SProxy "crActiveContractStates")

_csrDefinition :: forall t. Lens' (ContractSignatureResponse t) t
_csrDefinition = _ContractSignatureResponse <<< prop (SProxy :: SProxy "csrDefinition")

_csContract :: forall t. Lens' (ContractInstanceState t) ContractInstanceId
_csContract = _Newtype <<< prop (SProxy :: SProxy "csContract")

_csCurrentState :: forall t. Lens' (ContractInstanceState t) (PartiallyDecodedResponse ContractSCBRequest)
_csCurrentState = _Newtype <<< prop (SProxy :: SProxy "csCurrentState")

_csContractDefinition :: forall t. Lens' (ContractInstanceState t) t
_csContractDefinition = _ContractInstanceState <<< prop (SProxy :: SProxy "csContractDefinition")

_hooks :: forall t. Lens' (PartiallyDecodedResponse t) (Array (Request t))
_hooks = _Newtype <<< prop (SProxy :: SProxy "hooks")

_activeEndpoint :: Lens' ActiveEndpoint EndpointDescription
_activeEndpoint = _Newtype <<< prop (SProxy :: SProxy "aeDescription")

_contractActiveEndpoints :: Traversal' (PartiallyDecodedResponse ContractSCBRequest) EndpointDescription
_contractActiveEndpoints =
  _hooks
    <<< traversed
    <<< _rqRequest
    <<< _UserEndpointRequest
    <<< _activeEndpoint

_rqRequest :: forall t. Lens' (Request t) t
_rqRequest = _Newtype <<< prop (SProxy :: SProxy "rqRequest")

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

------------------------------------------------------------
toPropertyKey :: PropertyDescription -> PropertyKey
toPropertyKey (Preimage _ _) = PropertyKey "preimage"

toPropertyKey (Name _ _) = PropertyKey "name"

toPropertyKey (Description _ _) = PropertyKey "description"

toPropertyKey (Other name _ _) = PropertyKey name

_getPubKeyHash :: forall s r a. Newtype s { getPubKeyHash :: a | r } => Lens' s a
_getPubKeyHash = _Newtype <<< prop (SProxy :: SProxy "getPubKeyHash")

_propertyName :: Getter' Metadata.PropertyDescription (Maybe String)
_propertyName = to propertyName

propertyName :: Metadata.PropertyDescription -> (Maybe String)
propertyName (Metadata.Name name _) = Just name

propertyName _ = Nothing
