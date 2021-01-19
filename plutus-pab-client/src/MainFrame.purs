module MainFrame
  ( initialMainFrame
  , handleQuery
  , handleAction
  , initialState
  ) where

import Prelude hiding (div)
import Animation (class MonadAnimate, animate)
import Cardano.Metadata.Types (Property, PropertyKey, Subject, SubjectProperties(..))
import Chain.State (handleAction) as Chain
import Chain.Types (Action(FocusTx), AnnotatedBlockchain(..), _chainFocusAppearing)
import Chain.Types (initialState) as Chain
import Clipboard (class MonadClipboard)
import Clipboard as Clipboard
import Control.Monad.Reader (runReaderT)
import Control.Monad.State (class MonadState)
import Control.Monad.State.Extra (zoomStateT)
import Data.Array (filter, find)
import Data.Either (Either(..))
import Data.Foldable (foldr)
import Data.Lens (_1, _2, assign, modifying, to, use, view)
import Data.Lens.At (at)
import Data.Lens.Extra (peruse, toSetOf)
import Data.Lens.Index (ix)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.RawJson (RawJson(..))
import Data.Set (Set)
import Data.Set as Set
import Data.Traversable (for_, sequence, traverse_)
import Data.Tuple (Tuple(..))
import Effect.Aff.Class (class MonadAff)
import Foreign.Generic (encodeJSON)
import Halogen (Component, hoist)
import Halogen as H
import Halogen.HTML (HTML)
import Ledger.Ada (Ada(..))
import Ledger.Extra (adaToValue)
import Ledger.Value (Value)
import MonadApp (class MonadApp, activateContract, getFullReport, invokeEndpoint, log, runHalogenApp)
import Network.RemoteData (RemoteData(..), _Success)
import Network.RemoteData as RemoteData
import Network.StreamData as Stream
import Playground.Lenses (_endpointDescription, _schema)
import Playground.Types (FunctionSchema(..), _FunctionSchema)
import Plutus.PAB.Events.Contract (ContractInstanceState(..))
import Plutus.PAB.Types (ContractExe)
import Plutus.PAB.Webserver (SPParams_(..))
import Plutus.PAB.Webserver.Types (ContractSignatureResponse(..), StreamToClient(..))
import Prim.TypeError (class Warn, Text)
import Schema (FormSchema)
import Schema.Types (formArgumentToJson, toArgument)
import Schema.Types as Schema
import Servant.PureScript.Settings (SPSettings_, defaultSettings)
import Types (ContractSignatures, EndpointForm, HAction(..), Output, Query(..), State(..), StreamError(..), View(..), WebSocketStatus(..), WebStreamData, _annotatedBlockchain, _chainReport, _chainState, _contractActiveEndpoints, _contractReport, _contractSignatures, _contractStates, _crActiveContractStates, _crAvailableContracts, _csContract, _csCurrentState, _currentView, _events, _metadata, _webSocketMessage, _webSocketStatus, fromWebData, toPropertyKey)
import Validation (_argument)
import View as View
import Wallet.Types (EndpointDescription)
import WebSocket.Support (FromSocket)
import WebSocket.Support as WS

initialValue :: Value
initialValue = adaToValue $ Lovelace { getLovelace: zero }

initialState :: State
initialState =
  State
    { currentView: ActiveContracts
    , contractSignatures: Stream.NotAsked
    , chainReport: NotAsked
    , events: NotAsked
    , chainState: Chain.initialState
    , contractStates: Map.empty
    , webSocketMessage: Stream.NotAsked
    , webSocketStatus: WebSocketClosed Nothing
    , metadata: mempty
    }

------------------------------------------------------------
ajaxSettings :: SPSettings_ SPParams_
ajaxSettings = defaultSettings $ SPParams_ { baseURL: "/" }

initialMainFrame ::
  forall m.
  MonadAff m =>
  MonadClipboard m =>
  Component HTML Query HAction Output m
initialMainFrame =
  hoist (flip runReaderT ajaxSettings)
    $ H.mkComponent
        { initialState: const initialState
        , render: View.render
        , eval:
            H.mkEval
              { handleAction: runHalogenApp <<< handleAction
              , handleQuery: runHalogenApp <<< handleQuery
              , initialize: Just Init
              , receive: const Nothing
              , finalize: Nothing
              }
        }

handleQuery ::
  forall m a.
  MonadState State m =>
  MonadApp m =>
  Query a -> m (Maybe a)
handleQuery (ReceiveWebSocketMessage msg next) = do
  handleMessageFromSocket msg
  pure $ Just next

handleMessageFromSocket ::
  forall m.
  MonadState State m =>
  MonadApp m =>
  FromSocket StreamToClient -> m Unit
handleMessageFromSocket WS.WebSocketOpen = do
  assign _webSocketStatus WebSocketOpen

handleMessageFromSocket (WS.ReceiveMessage (Right msg)) = case msg of
  NewChainReport report -> assign _chainReport (Success report)
  NewContractReport report -> do
    assign _contractSignatures (Stream.Success (view _crAvailableContracts report))
    traverse_ updateFormsForContractInstance
      (view _crActiveContractStates report)
  NewChainEvents events -> assign _events (Success events)
  ErrorResponse err -> assign _webSocketMessage $ Stream.Failure $ ServerError err
  FetchedProperty subject property -> do
    log $ "Websocket fetch property: " <> show msg
    modifying _metadata (upsertProperty subject property)
  FetchedProperties (SubjectProperties subject properties) -> do
    log $ "Websocket fetch properties: " <> show msg
    modifying _metadata (\m -> foldr (upsertProperty subject) m properties)

handleMessageFromSocket (WS.ReceiveMessage (Left err)) = assign _webSocketMessage $ Stream.Failure $ DecodingError err

handleMessageFromSocket (WS.WebSocketClosed closeEvent) = do
  assign _webSocketStatus (WebSocketClosed (Just closeEvent))

upsertProperty :: Subject -> Property -> Map Subject (Map PropertyKey Property) -> Map Subject (Map PropertyKey Property)
upsertProperty subject property =
  Map.insertWith append subject
    $ Map.singleton (toPropertyKey property) property

handleAction ::
  forall m.
  MonadApp m =>
  MonadAnimate m State =>
  MonadClipboard m =>
  MonadState State m =>
  HAction -> m Unit
handleAction Init = handleAction LoadFullReport

handleAction (ChangeView view) = do
  assign _currentView view

handleAction (ActivateContract contract) = do
  modifying _contractSignatures Stream.refreshing
  activateContract contract
  modifying _contractSignatures Stream.refreshed

handleAction LoadFullReport = do
  assignFullReportData Loading
  fullReportResult <- getFullReport
  assignFullReportData fullReportResult
  traverse_ updateFormsForContractInstance
    (view (_Success <<< _contractReport <<< _crActiveContractStates) fullReportResult)
  where
  assignFullReportData value = do
    assign _contractSignatures
      (fromWebData (view (_contractReport <<< _crAvailableContracts) <$> value))
    assign _chainReport (view _chainReport <$> value)
    assign _events (view _events <$> value)

handleAction (ChainAction subaction) = do
  mAnnotatedBlockchain <-
    peruse (_chainReport <<< RemoteData._Success <<< _annotatedBlockchain <<< to AnnotatedBlockchain)
  let
    wrapper ::
      Warn (Text "The question, 'Should we animate this?' feels like it belongs in the Chain module. Not here.") =>
      m Unit -> m Unit
    wrapper = case subaction of
      (FocusTx _) -> animate (_chainState <<< _chainFocusAppearing)
      _ -> identity
  wrapper
    $ zoomStateT _chainState
    $ Chain.handleAction subaction mAnnotatedBlockchain

handleAction (ClipboardAction subaction) = Clipboard.handleAction subaction

handleAction (ChangeContractEndpointCall contractInstanceId endpointIndex subaction) = do
  modifying
    ( _contractStates
        <<< ix contractInstanceId
        <<< Stream._Success
        <<< _2
        <<< ix endpointIndex
        <<< _argument
    )
    (Schema.handleFormEvent initialValue subaction)

handleAction (InvokeContractEndpoint contractInstanceId endpointForm) = do
  let
    endpointDescription :: EndpointDescription
    endpointDescription = view (_schema <<< _FunctionSchema <<< _endpointDescription) endpointForm

    mEncodedForm :: Maybe RawJson
    mEncodedForm = RawJson <<< encodeJSON <$> formArgumentToJson (view _argument endpointForm)
  for_ mEncodedForm
    $ \encodedForm -> do
        assign (_contractStates <<< at contractInstanceId) (Just Stream.Loading)
        invokeEndpoint encodedForm contractInstanceId endpointDescription

updateFormsForContractInstance ::
  forall m.
  MonadState State m =>
  ContractInstanceState ContractExe -> m Unit
updateFormsForContractInstance newContractInstance = do
  let
    csContractId = view _csContract newContractInstance
  oldContractInstance :: Maybe (ContractInstanceState ContractExe) <-
    peruse
      ( _contractStates
          <<< ix csContractId
          <<< Stream._Success
          <<< _1
      )
  when (oldContractInstance /= Just newContractInstance) do
    contractSignatures :: WebStreamData ContractSignatures <- use _contractSignatures
    let
      newForms :: Maybe (WebStreamData (Array EndpointForm))
      newForms = sequence $ createNewEndpointForms <$> contractSignatures <*> pure newContractInstance
    assign (_contractStates <<< at csContractId)
      (map (Tuple newContractInstance) <$> newForms)

createNewEndpointForms ::
  ContractSignatures ->
  ContractInstanceState ContractExe ->
  Maybe (Array EndpointForm)
createNewEndpointForms contractSignatures instanceState = createEndpointForms instanceState <$> matchingSignature
  where
  matchingSignature :: Maybe (ContractSignatureResponse ContractExe)
  matchingSignature = getMatchingSignature instanceState contractSignatures

createEndpointForms ::
  forall t.
  ContractInstanceState t ->
  ContractSignatureResponse t ->
  Array EndpointForm
createEndpointForms contractState = signatureToForms
  where
  activeEndpoints :: Set EndpointDescription
  activeEndpoints =
    toSetOf
      ( _csCurrentState
          <<< _contractActiveEndpoints
      )
      contractState

  isActive :: FunctionSchema FormSchema -> Boolean
  isActive (FunctionSchema { endpointDescription }) = Set.member endpointDescription activeEndpoints

  signatureToForms :: ContractSignatureResponse t -> Array EndpointForm
  signatureToForms (ContractSignatureResponse { csrSchemas }) = signatureToForm <$> filter isActive csrSchemas

  signatureToForm :: FunctionSchema FormSchema -> EndpointForm
  signatureToForm schema =
    { argument: toArgument initialValue $ view (_FunctionSchema <<< _argument) schema
    , schema
    }

getMatchingSignature ::
  forall t.
  Eq t =>
  ContractInstanceState t ->
  Array (ContractSignatureResponse t) ->
  Maybe (ContractSignatureResponse t)
getMatchingSignature (ContractInstanceState { csContractDefinition }) = find isMatch
  where
  isMatch (ContractSignatureResponse { csrDefinition }) = csrDefinition == csContractDefinition
