module MainFrame
  ( initialMainFrame
  , handleQuery
  , handleAction
  , initialState
  ) where

import Plutus.SCB.Webserver (SPParams_(..))
import Plutus.SCB.Webserver.Types (ContractSignatureResponse(..), FullReport, StreamToClient(..), StreamToServer(..))
import Prelude hiding (div)
import Types (EndpointForm, HAction(..), Output, Query(..), State(..), View(..), _annotatedBlockchain, _chainReport, _chainState, _contractActiveEndpoints, _contractReport, _contractSignatures, _contractStates, _crAvailableContracts, _csContract, _csCurrentState, _currentView, _events, _fullReport, _webSocketMessage)
import Animation (class MonadAnimate, animate)
import Chain.Eval (handleAction) as Chain
import Chain.Types (Action(..), AnnotatedBlockchain(..), _chainFocusAppearing)
import Chain.Types (initialState) as Chain
import Clipboard (class MonadClipboard)
import Control.Monad.Reader (runReaderT)
import Control.Monad.State (class MonadState)
import Control.Monad.State.Extra (zoomStateT)
import Data.Array (filter)
import Data.Either (Either(..))
import Data.Foldable (traverse_)
import Data.Lens (_1, _2, assign, findOf, modifying, to, traversed, view)
import Data.Lens.At (at)
import Data.Lens.Extra (peruse, toSetOf)
import Data.Lens.Index (ix)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.RawJson (RawJson(..))
import Data.Set (Set)
import Data.Set as Set
import Data.Traversable (for_)
import Data.Tuple (Tuple(..))
import Effect.Aff.Class (class MonadAff)
import Foreign.Generic (encodeJSON)
import Halogen (Component, hoist)
import Halogen as H
import Halogen.HTML (HTML)
import Language.Plutus.Contract.Effects.ExposeEndpoint (EndpointDescription)
import Ledger.Ada (Ada(..))
import Ledger.Extra (adaToValue)
import Ledger.Value (Value)
import MonadApp (class MonadApp, activateContract, getContractSignature, getFullReport, invokeEndpoint, log, runHalogenApp, sendWebSocketMessage)
import Network.RemoteData (RemoteData(..), _Success)
import Network.RemoteData as RemoteData
import Playground.Lenses (_endpointDescription, _schema)
import Playground.Types (FunctionSchema(..), _FunctionSchema)
import Plutus.SCB.Events.Contract (ContractInstanceState(..))
import Plutus.SCB.Types (ContractExe)
import Prim.TypeError (class Warn, Text)
import Schema (FormSchema)
import Schema.Types (formArgumentToJson, toArgument)
import Schema.Types as Schema
import Servant.PureScript.Settings (SPSettings_, defaultSettings)
import Validation (_argument)
import View as View
import WebSocket.Support as WS

initialValue :: Value
initialValue = adaToValue $ Lovelace { getLovelace: 0 }

initialState :: State
initialState =
  State
    { currentView: ActiveContracts
    , fullReport: NotAsked
    , chainState: Chain.initialState
    , contractSignatures: Map.empty
    , webSocketMessage: NotAsked
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
  Warn (Text "Handle WebSocket errors.") =>
  Warn (Text "Handle WebSocket disconnections.") =>
  MonadState State m =>
  MonadApp m =>
  Query a -> m (Maybe a)
handleQuery (ReceiveWebSocketMessage (WS.ReceiveMessage msg) next) = do
  case msg of
    Right (NewChainReport report) -> assign (_fullReport <<< _Success <<< _chainReport) report
    Right (NewContractReport report) -> do
      assign (_fullReport <<< _Success <<< _contractReport) report
      traverse_ updateFormsForContractInstance
        (view _contractStates report)
    Right (NewChainEvents events) -> assign (_fullReport <<< _Success <<< _events) events
    Right (Echo _) -> pure unit
    Right (ErrorResponse _) -> pure unit
    Left err -> pure unit
  assign _webSocketMessage $ RemoteData.fromEither msg
  pure $ Just next

handleQuery (ReceiveWebSocketMessage WS.WebSocketClosed next) = do
  log "Closed"
  pure $ Just next

handleAction ::
  forall m.
  MonadApp m =>
  MonadAnimate m State =>
  MonadClipboard m =>
  MonadState State m =>
  HAction -> m Unit
handleAction Init = handleAction LoadFullReport

handleAction (ChangeView view) = do
  sendWebSocketMessage $ Ping $ show view
  assign _currentView view

handleAction (ActivateContract contract) = activateContract contract

handleAction LoadFullReport = do
  assign _fullReport Loading
  fullReportResult <- getFullReport
  assign _fullReport fullReportResult
  for_ fullReportResult
    ( \fullReport ->
        traverse_ updateFormsForContractInstance
          (view (_contractReport <<< _contractStates) fullReport)
    )

handleAction (ChainAction subaction) = do
  mAnnotatedBlockchain <-
    peruse (_fullReport <<< _Success <<< _chainReport <<< _annotatedBlockchain <<< to AnnotatedBlockchain)
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

handleAction (ChangeContractEndpointCall contractInstanceId endpointIndex subaction) = do
  modifying
    ( _contractSignatures
        <<< ix contractInstanceId
        <<< _Success
        <<< _2
        <<< ix endpointIndex
        <<< _argument
    )
    (Schema.handleFormEvent initialValue subaction)

handleAction (InvokeContractEndpoint contractInstanceId endpointForm) = do
  let
    endpointDescription :: EndpointDescription
    endpointDescription = view (_schema <<< _FunctionSchema <<< _endpointDescription) endpointForm

    encodedForm :: Maybe RawJson
    encodedForm = RawJson <<< encodeJSON <$> formArgumentToJson (view _argument endpointForm)
  for_ encodedForm
    $ \argument -> do
        assign (_contractSignatures <<< at contractInstanceId) (Just Loading)
        invokeEndpoint argument contractInstanceId endpointDescription

updateFormsForContractInstance ::
  forall m.
  MonadApp m =>
  MonadState State m =>
  ContractInstanceState ContractExe -> m Unit
updateFormsForContractInstance newContractInstance = do
  let
    csContractId = view _csContract newContractInstance
  oldContractInstance :: Maybe (ContractInstanceState ContractExe) <-
    peruse
      ( _contractSignatures
          <<< ix csContractId
          <<< _Success
          <<< _1
      )
  when (oldContractInstance /= Just newContractInstance)
    $ do
        contractSchema <- getContractSignature $ view _csContract newContractInstance
        assign (_contractSignatures <<< at csContractId)
          (Just (Tuple newContractInstance <$> (createEndpointForms newContractInstance <$> contractSchema)))

createNewEndpointFormsM ::
  forall m.
  Monad m =>
  m (FullReport ContractExe) ->
  m (ContractInstanceState ContractExe) ->
  m (Maybe (Array EndpointForm))
createNewEndpointFormsM mFullReport mInstanceState = do
  fullReport <- mFullReport
  instanceState <- mInstanceState
  let
    matchingSignature :: Maybe (ContractSignatureResponse ContractExe)
    matchingSignature = getMatchingSignature instanceState fullReport

    newForms :: Maybe (Array EndpointForm)
    newForms = createEndpointForms instanceState <$> matchingSignature
  pure newForms

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
  FullReport t ->
  Maybe (ContractSignatureResponse t)
getMatchingSignature (ContractInstanceState { csContractDefinition }) =
  findOf
    ( _contractReport
        <<< _crAvailableContracts
        <<< traversed
    )
    isMatch
  where
  isMatch (ContractSignatureResponse { csrDefinition }) = csrDefinition == csContractDefinition
