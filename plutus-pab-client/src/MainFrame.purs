module MainFrame
  ( initialMainFrame
  , handleQuery
  , handleAction
  , initialState
  ) where

import Prelude hiding (div)
import Animation (class MonadAnimate, animate)
import Chain.State (handleAction) as Chain
import Chain.Types (Action(FocusTx), AnnotatedBlockchain(..), _chainFocusAppearing)
import Chain.Types (initialState) as Chain
import Clipboard (class MonadClipboard)
import Clipboard as Clipboard
import Control.Monad.Reader (runReaderT)
import Control.Monad.State (class MonadState)
import Control.Monad.State.Extra (zoomStateT)
import Data.Array (filter, find)
import Data.BigInteger as BigInteger
import Data.Either (Either(..))
import Data.Lens (Lens', _1, _2, assign, modifying, to, use, view, preview)
import Data.Lens.At (at)
import Data.Lens.Extra (peruse, toSetOf)
import Data.Lens.Index (ix)
import Data.Map as Map
import Data.Maybe (Maybe(..), maybe)
import Data.RawJson (RawJson(..))
import Data.Set (Set)
import Data.Set as Set
import Data.Traversable (for_, sequence, traverse_)
import Data.Tuple (Tuple(..))
import Data.Tuple.Nested ((/\))
import Effect.Aff.Class (class MonadAff)
import Foreign.Generic (encodeJSON)
import Halogen (Component, hoist)
import Halogen as H
import Halogen.HTML (HTML)
import Ledger.Extra (adaToValue)
import MonadApp (class MonadApp, activateContract, getFullReport, invokeEndpoint, runHalogenApp, getContractDefinitions, getContractInstances, getContractInstanceStatus)
import Network.RemoteData (RemoteData(..))
import Network.RemoteData as RemoteData
import Network.StreamData as Stream
import Playground.Lenses (_endpointDescription, _schema)
import Playground.Types (FunctionSchema(..), _FunctionSchema)
import Plutus.Contract.Effects (ActiveEndpoint)
import Plutus.PAB.Events.ContractInstanceState (PartiallyDecodedResponse)
import Plutus.PAB.Webserver (SPParams_(..))
import Plutus.PAB.Webserver.Types (ContractInstanceClientState(..), ContractSignatureResponse(..), CombinedWSStreamToClient, ContractActivationArgs(..))
import Plutus.V1.Ledger.Ada (Ada(..))
import Plutus.V1.Ledger.Value (Value)
import Prim.TypeError (class Warn, Text)
import Schema (FormSchema)
import Schema.Types (formArgumentToJson, toArgument)
import Schema.Types as Schema
import Servant.PureScript.Settings (SPSettings_, defaultSettings)
import Types (HAction(..), Output, Query(..), State(..), StreamError(..), View(..), WebSocketStatus(..), ContractSignatures(..), EndpointForm, WebStreamData, _webSocketMessage, _webSocketStatus, _annotatedBlockchain, _chainReport, _chainState, _contractActiveEndpoints, _contractSignatures, _contractStates, _currentView, _csContract, _csCurrentState, fromWebData)
import Validation (_argument)
import View as View
import Wallet.Emulator.Wallet (Wallet(..))
import Wallet.Types (EndpointDescription)
import WebSocket.Support (FromSocket)
import WebSocket.Support as WS
import ContractExample (ExampleContracts)

-- | The PAB has been completely rewritten, and the PAB client will soon follow. The immediate
--   priority is the new Marlowe dashboard, however, so in the meantime large chunks of the PAB
--   client are commented out just so that it compiles.
initialValue :: Value
initialValue = adaToValue $ Lovelace { getLovelace: zero }

initialState :: State ExampleContracts
initialState =
  State
    { currentView: ActiveContracts
    , contractSignatures: Stream.NotAsked
    , chainReport: NotAsked
    , chainState: Chain.initialState
    , contractStates: Map.empty
    , webSocketMessage: Stream.NotAsked
    , webSocketStatus: WebSocketClosed Nothing
    }

------------------------------------------------------------
ajaxSettings :: SPSettings_ SPParams_
ajaxSettings = defaultSettings $ SPParams_ { baseURL: "/" }

initialMainFrame ::
  forall m.
  MonadAff m =>
  MonadClipboard m =>
  Component HTML Query (HAction ExampleContracts) Output m
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
  MonadState (State ExampleContracts) m =>
  MonadApp m =>
  Query a -> m (Maybe a)
handleQuery (ReceiveWebSocketMessage msg next) = do
  handleMessageFromSocket msg
  pure $ Just next

handleMessageFromSocket ::
  forall m.
  MonadState (State ExampleContracts) m =>
  MonadApp m =>
  FromSocket CombinedWSStreamToClient -> m Unit
handleMessageFromSocket WS.WebSocketOpen = do
  assign _webSocketStatus WebSocketOpen

handleMessageFromSocket (WS.ReceiveMessage (Right msg)) = pure unit

--case msg of
--NewChainReport report -> assign _chainReport (Success report)
--NewContractReport report -> do
--  assign _contractSignatures (Stream.Success (view _crAvailableContracts report))
--  traverse_ updateFormsForContractInstance
--    (view _crActiveContractStates report)
--NewChainEvents events -> assign _events (Success events)
--ErrorResponse err -> assign _webSocketMessage $ Stream.Failure $ ServerError err
--FetchedProperty subject property -> do
--  log $ "Websocket fetch property: " <> show msg
--  modifying _metadata (upsertProperty subject property)
--FetchedProperties (SubjectProperties subject properties) -> do
--  log $ "Websocket fetch properties: " <> show msg
--  modifying _metadata (\m -> foldr (upsertProperty subject) m properties)
handleMessageFromSocket (WS.ReceiveMessage (Left err)) = assign _webSocketMessage $ Stream.Failure $ DecodingError err

handleMessageFromSocket (WS.WebSocketClosed closeEvent) = do
  assign _webSocketStatus (WebSocketClosed (Just closeEvent))

handleAction ::
  forall m.
  MonadApp m =>
  MonadAnimate m (State ExampleContracts) =>
  MonadClipboard m =>
  MonadState (State ExampleContracts) m =>
  (HAction ExampleContracts) -> m Unit
handleAction Init = handleAction LoadFullReport

handleAction (ChangeView view) = do
  assign _currentView view

handleAction (ActivateContract contract) = do
  modifying _contractSignatures Stream.refreshing
  let
    defWallet = Wallet { getWallet: BigInteger.fromInt 1 }
  contractInstanceId <- activateContract $ ContractActivationArgs { caID: contract, caWallet: defWallet }
  for_ (preview RemoteData._Success contractInstanceId)
    $ \cid -> do
        clientState <- map fromWebData $ getContractInstanceStatus cid
        contractSignatures :: WebStreamData (ContractSignatures ExampleContracts) <- use _contractSignatures
        let
          loadFormFromClientState cs =
            let
              newForms = sequence $ createNewEndpointForms <$> contractSignatures <*> pure cs
            in
              cs /\ maybe [] (view Stream._Refreshing) newForms
        modifying _contractStates $ (<>) $ Map.singleton cid $ map loadFormFromClientState clientState
        traverse_ updateFormsForContractInstance clientState
  modifying _contractSignatures Stream.refreshed

handleAction LoadFullReport = do
  assignFullReportData Loading
  contractdefs <- getContractDefinitions
  assign _contractSignatures (map (\a -> ContractSignatures { unContractSignatures: a }) $ fromWebData contractdefs)
  contractInstances <- view (RemoteData._Success) <$> getContractInstances
  traverse_ updateFormsForContractInstance contractInstances
  fullReportResult <- getFullReport
  assignFullReportData fullReportResult
  where
  assignFullReportData value = do
    assign _chainReport (view _chainReport <$> value)

-- assign _events (view _events <$> value)
handleAction (ChainAction subaction) = do
  mAnnotatedBlockchain <-
    peruse (_chainReport <<< RemoteData._Success <<< _annotatedBlockchain <<< to AnnotatedBlockchain)
  let
    wrapper ::
      Warn (Text "The question, 'Should we animate this?' feels like it belongs in the Chain module. Not here.") =>
      m Unit -> m Unit
    wrapper = case subaction of
      (FocusTx _) -> animate (_chainState <<< _chainFocusAppearing :: Lens' (State ExampleContracts) Boolean)
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
  MonadState (State ExampleContracts) m =>
  ContractInstanceClientState ExampleContracts -> m Unit
updateFormsForContractInstance newContractInstance = do
  let
    csContractId = view _csContract newContractInstance
  oldContractInstance :: Maybe (PartiallyDecodedResponse ActiveEndpoint) <-
    peruse
      ( _contractStates
          <<< ix csContractId
          <<< Stream._Success
          <<< _1
          <<< _csCurrentState
      )
  when (oldContractInstance /= Just (view _csCurrentState newContractInstance)) do
    contractSignatures :: WebStreamData (ContractSignatures ExampleContracts) <- use _contractSignatures
    let
      newForms :: Maybe (WebStreamData (Array EndpointForm))
      newForms = sequence $ createNewEndpointForms <$> contractSignatures <*> pure newContractInstance
    assign (_contractStates <<< at csContractId)
      (map (Tuple newContractInstance) <$> newForms)

createNewEndpointForms ::
  ContractSignatures ExampleContracts ->
  ContractInstanceClientState ExampleContracts ->
  Maybe (Array EndpointForm)
createNewEndpointForms contractSignatures instanceState = createEndpointForms instanceState <$> matchingSignature
  where
  matchingSignature :: Maybe (ContractSignatureResponse ExampleContracts)
  matchingSignature = getMatchingSignature instanceState contractSignatures

createEndpointForms ::
  forall t.
  ContractInstanceClientState t ->
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
  forall a.
  Eq a =>
  ContractInstanceClientState a ->
  ContractSignatures a ->
  Maybe (ContractSignatureResponse a)
getMatchingSignature (ContractInstanceClientState { cicDefinition }) (ContractSignatures { unContractSignatures }) = find isMatch unContractSignatures
  where
  isMatch (ContractSignatureResponse { csrDefinition }) = csrDefinition == cicDefinition
