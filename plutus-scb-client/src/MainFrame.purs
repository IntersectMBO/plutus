module MainFrame
  ( initialMainFrame
  , handleAction
  , initialState
  ) where

import Prelude
import Animation (class MonadAnimate, animate)
import Chain.Eval (handleAction) as Chain
import Chain.Types (Action(..), AnnotatedBlockchain(..), _chainFocusAppearing)
import Chain.Types (initialState) as Chain
import Clipboard (class MonadClipboard)
import Control.Monad.Except.Trans (ExceptT, runExceptT)
import Control.Monad.Reader (class MonadAsk, runReaderT)
import Control.Monad.State (class MonadState)
import Control.Monad.State.Extra (zoomStateT)
import Data.Foldable (traverse_)
import Data.Lens (assign, modifying, to, toArrayOf, traversed, view)
import Data.Lens.At (at)
import Data.Lens.Extra (peruse)
import Data.Lens.Index (ix)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.RawJson (RawJson(..))
import Data.Traversable (for_)
import Effect.Aff.Class (class MonadAff)
import Effect.Class (class MonadEffect)
import Foreign.Generic (encodeJSON)
import Halogen (Component, hoist)
import Halogen as H
import Halogen.HTML (HTML)
import Language.Plutus.Contract.Effects.ExposeEndpoint (EndpointDescription)
import Ledger.Ada (Ada(..))
import Ledger.Extra (adaToValue)
import Ledger.Value (Value)
import Network.RemoteData (RemoteData(..), _Success)
import Network.RemoteData as RemoteData
import Playground.Lenses (_endpointDescription, _getEndpointDescription, _schema)
import Playground.Types (FunctionSchema, _FunctionSchema)
import Plutus.SCB.Webserver (SPParams_(..), getApiContractByContractinstanceidSchema, getApiFullreport, postApiContractActivate, postApiContractByContractinstanceidEndpointByEndpointname)
import Plutus.SCB.Webserver.Types (ContractSignatureResponse(..))
import Schema (FormSchema)
import Schema.Types (formArgumentToJson, toArgument)
import Schema.Types as Schema
import Servant.PureScript.Ajax (AjaxError)
import Servant.PureScript.Settings (SPSettings_, defaultSettings)
import Types (EndpointForm, HAction(..), Query, State(..), View(..), WebData, _annotatedBlockchain, _chainReport, _chainState, _contractInstanceIdString, _contractReport, _contractSignatures, _csContract, _currentView, _fullReport, _latestContractStatuses)
import Validation (_argument)
import View as View

initialValue :: Value
initialValue = adaToValue $ Lovelace { getLovelace: 0 }

initialState :: State
initialState =
  State
    { currentView: ActiveContracts
    , fullReport: NotAsked
    , chainState: Chain.initialState
    , contractSignatures: Map.empty
    }

------------------------------------------------------------
ajaxSettings :: SPSettings_ SPParams_
ajaxSettings = defaultSettings $ SPParams_ { baseURL: "/" }

initialMainFrame ::
  forall m.
  MonadAff m =>
  MonadClipboard m =>
  Component HTML Query HAction Void m
initialMainFrame =
  hoist (flip runReaderT ajaxSettings)
    $ H.mkComponent
        { initialState: const initialState
        , render: View.render
        , eval:
          H.mkEval
            { handleAction: handleAction
            , handleQuery: const $ pure Nothing
            , initialize: Just Init
            , receive: const Nothing
            , finalize: Nothing
            }
        }

handleAction ::
  forall m.
  MonadState State m =>
  MonadAff m =>
  MonadAnimate m State =>
  MonadClipboard m =>
  MonadAsk (SPSettings_ SPParams_) m =>
  MonadEffect m =>
  HAction -> m Unit
handleAction Init = handleAction LoadFullReport

handleAction (ChangeView view) = assign _currentView view

handleAction (ActivateContract contract) = do
  result <- runAjax $ postApiContractActivate contract
  handleAction LoadFullReport

handleAction LoadFullReport = do
  assign _fullReport Loading
  reportResult <- runAjax getApiFullreport
  assign _fullReport reportResult
  case reportResult of
    Success fullReport ->
      traverse_
        ( \instanceId -> do
            let
              uuid = view _contractInstanceIdString instanceId
            contractSchema <- runAjax $ getApiContractByContractinstanceidSchema uuid
            modifying (_contractSignatures <<< at instanceId) (Just <<< upsertEndpointForm contractSchema)
        )
        (toArrayOf (_contractReport <<< _latestContractStatuses <<< traversed <<< _csContract) fullReport)
    _ -> pure unit
  pure unit

handleAction (ChainAction subaction) = do
  mAnnotatedBlockchain <-
    peruse (_fullReport <<< _Success <<< _chainReport <<< _annotatedBlockchain <<< to AnnotatedBlockchain)
  let
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
        result <-
          runAjax
            $ let
                instanceId = view _contractInstanceIdString contractInstanceId

                endpoint = view _getEndpointDescription endpointDescription
              in
                postApiContractByContractinstanceidEndpointByEndpointname argument instanceId endpoint
        modifying (_contractSignatures <<< at contractInstanceId) (Just <<< upsertEndpointForm result)
        case result of
          Success _ -> handleAction LoadFullReport
          _ -> pure unit

upsertEndpointForm ::
  forall t.
  WebData (ContractSignatureResponse t) ->
  Maybe (WebData (Array EndpointForm)) ->
  WebData (Array EndpointForm)
upsertEndpointForm response existing = responseToForms <$> response
  where
  responseToForms :: ContractSignatureResponse t -> Array EndpointForm
  responseToForms (ContractSignatureResponse signatures) = signatureToForm <$> signatures

  signatureToForm :: FunctionSchema FormSchema -> EndpointForm
  signatureToForm schema =
    { argument: toArgument initialValue $ view (_FunctionSchema <<< _argument) schema
    , schema: schema
    }

runAjax :: forall m a. Functor m => ExceptT AjaxError m a -> m (WebData a)
runAjax action = RemoteData.fromEither <$> runExceptT action
