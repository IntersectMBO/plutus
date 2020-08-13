module MainFrame
  ( mkMainFrame
  , handleAction
  , mkInitialState
  ) where

import Prelude
import Ace.Types (Annotation)
import AjaxUtils (renderForeignErrors)
import Analytics (Event, defaultEvent, trackEvent)
import Animation (class MonadAnimate, animate)
import Chain.Eval (handleAction) as Chain
import Chain.Types (Action(..), AnnotatedBlockchain(..), _chainFocusAppearing)
import Chain.Types (initialState) as Chain
import Clipboard (class MonadClipboard)
import Clipboard as Clipboard
import Control.Monad.Error.Class (class MonadThrow)
import Control.Monad.Error.Extra (mapError)
import Control.Monad.Except.Extra (noteT)
import Control.Monad.Except.Trans (ExceptT(..), except, mapExceptT, withExceptT, runExceptT)
import Control.Monad.Maybe.Extra (hoistMaybe)
import Control.Monad.Maybe.Trans (MaybeT(..), runMaybeT)
import Control.Monad.Reader (class MonadAsk, runReaderT)
import Control.Monad.State.Class (class MonadState)
import Control.Monad.State.Extra (zoomStateT)
import Control.Monad.Trans.Class (lift)
import Cursor (_current)
import Cursor as Cursor
import Data.Array (catMaybes, (..))
import Data.Array (deleteAt, snoc) as Array
import Data.Array.Extra (move) as Array
import Data.Bifunctor (lmap)
import Data.Either (Either(..), note)
import Data.Json.JsonEither (JsonEither(..), _JsonEither)
import Data.Lens (Traversal', _Just, _Right, assign, modifying, over, to, traversed, use)
import Data.Lens.Extra (peruse)
import Data.Lens.Fold (maximumOf, preview)
import Data.Lens.Index (ix)
import Data.Lens.Iso.Newtype (_Newtype)
import Data.Maybe (Maybe(..), fromMaybe)
import Data.MediaType.Common (textPlain)
import Data.Newtype (unwrap)
import Data.String as String
import Editor as Editor
import Effect (Effect)
import Effect.Aff.Class (class MonadAff)
import Effect.Class (class MonadEffect, liftEffect)
import Effect.Exception (Error, error)
import Foreign.Generic (decodeJSON)
import Gist (_GistId, gistFileContent, gistId)
import Gists (GistAction(..))
import Gists as Gists
import Halogen (Component, hoist)
import Halogen as H
import Halogen.HTML (HTML)
import Halogen.Query (HalogenM)
import Language.Haskell.Interpreter (CompilationError(..), InterpreterError(..), InterpreterResult, SourceCode(..), _InterpreterResult)
import Ledger.Value (Value)
import MonadApp (class MonadApp, editorGetContents, editorHandleAction, editorSetAnnotations, editorSetContents, getGistByGistId, getOauthStatus, patchGistByGistId, postContract, postEvaluation, postGist, preventDefault, resizeBalancesChart, runHalogenApp, saveBuffer, setDataTransferData, setDropEffect)
import Network.RemoteData (RemoteData(..), _Success, isSuccess)
import Playground.Gists (mkNewGist, playgroundGistFile, simulationGistFile)
import Playground.Server (SPParams_(..))
import Playground.Types (ContractCall, ContractDemo(..), KnownCurrency, Simulation(..), SimulatorWallet(..), _CallEndpoint, _FunctionSchema)
import Schema.Types (ActionEvent(..), FormArgument, SimulationAction(..), mkInitialValue)
import Schema.Types as Schema
import Servant.PureScript.Ajax (errorToString)
import Servant.PureScript.Settings (SPSettings_, defaultSettings)
import StaticData (mkContractDemos)
import StaticData as StaticData
import Types (_simulationActions, ChildSlots, DragAndDropEventType(..), HAction(..), Query, State(..), View(..), WalletEvent(..), WebData, _actionDrag, _authStatus, _blockchainVisualisationState, _compilationResult, _contractDemos, _createGistResult, _currentView, _evaluationResult, _functionSchema, _gistUrl, _knownCurrencies, _result, _resultRollup, _simulationWallets, _simulations, _simulatorWalletBalance, _simulatorWalletWallet, _successfulCompilationResult, _walletId, getKnownCurrencies, toEvaluation)
import Validation (_argumentValues, _argument)
import ValueEditor (ValueEvent(..))
import View as View
import Wallet.Emulator.Wallet (Wallet(Wallet))
import Web.HTML.Event.DataTransfer as DataTransfer

mkSimulatorWallet :: Array KnownCurrency -> Int -> SimulatorWallet
mkSimulatorWallet currencies walletId =
  SimulatorWallet
    { simulatorWalletWallet: Wallet { getWallet: walletId }
    , simulatorWalletBalance: mkInitialValue currencies 10
    }

mkSimulation :: Array KnownCurrency -> String -> Simulation
mkSimulation simulationCurrencies simulationName =
  Simulation
    { simulationName
    , simulationActions: []
    , simulationWallets: mkSimulatorWallet simulationCurrencies <$> 1 .. 2
    }

mkInitialState :: forall m. MonadThrow Error m => Editor.Preferences -> m State
mkInitialState editorPreferences = do
  contractDemos <- mapError (\e -> error $ "Could not load demo scripts. Parsing errors: " <> show e) mkContractDemos
  pure
    $ State
        { currentView: Editor
        , editorPreferences
        , contractDemos
        , compilationResult: NotAsked
        , simulations: Cursor.empty
        , actionDrag: Nothing
        , evaluationResult: NotAsked
        , authStatus: NotAsked
        , createGistResult: NotAsked
        , gistUrl: Nothing
        , blockchainVisualisationState: Chain.initialState
        }

------------------------------------------------------------
ajaxSettings :: SPSettings_ SPParams_
ajaxSettings = defaultSettings $ SPParams_ { baseURL: "/api/" }

mkMainFrame ::
  forall m n.
  MonadThrow Error n =>
  MonadEffect n =>
  MonadAff m =>
  n (Component HTML Query HAction Void m)
mkMainFrame = do
  editorPreferences <- Editor.loadPreferences
  initialState <- mkInitialState editorPreferences
  pure $ hoist (flip runReaderT ajaxSettings)
    $ H.mkComponent
        { initialState: const initialState
        , render: View.render
        , eval:
          H.mkEval
            { handleAction: handleActionWithAnalyticsTracking
            , handleQuery: const $ pure Nothing
            , initialize: Just CheckAuthStatus
            , receive: const Nothing
            , finalize: Nothing
            }
        }

handleActionWithAnalyticsTracking ::
  forall m.
  MonadEffect m =>
  MonadAsk (SPSettings_ SPParams_) m =>
  MonadAff m =>
  HAction -> HalogenM State HAction ChildSlots Void m Unit
handleActionWithAnalyticsTracking action = do
  liftEffect $ analyticsTracking action
  runHalogenApp $ handleAction action

analyticsTracking :: HAction -> Effect Unit
analyticsTracking action = do
  case toEvent action of
    Nothing -> pure unit
    Just event -> trackEvent event

-- | Here we decide which top-level queries to track as GA events, and
-- how to classify them.
toEvent :: HAction -> Maybe Event
toEvent Mounted = Just $ defaultEvent "Mounted"

toEvent (EditorAction (Editor.HandleDropEvent _)) = Just $ defaultEvent "DropScript"

toEvent (EditorAction action) = Just $ (defaultEvent "ConfigureEditor")

toEvent CompileProgram = Just $ defaultEvent "CompileProgram"

toEvent (HandleBalancesChartMessage _) = Nothing

toEvent CheckAuthStatus = Nothing

toEvent (GistAction PublishGist) = Just $ (defaultEvent "Publish") { category = Just "Gist" }

toEvent (GistAction (SetGistUrl _)) = Nothing

toEvent (GistAction LoadGist) = Just $ (defaultEvent "LoadGist") { category = Just "Gist" }

toEvent (ChangeView view) = Just $ (defaultEvent "View") { label = Just $ show view }

toEvent (LoadScript script) = Just $ (defaultEvent "LoadScript") { label = Just script }

toEvent AddSimulationSlot = Just $ (defaultEvent "AddSimulationSlot") { category = Just "Simulation" }

toEvent (SetSimulationSlot _) = Just $ (defaultEvent "SetSimulationSlot") { category = Just "Simulation" }

toEvent (RemoveSimulationSlot _) = Just $ (defaultEvent "RemoveSimulationSlot") { category = Just "Simulation" }

toEvent (ModifyWallets AddWallet) = Just $ (defaultEvent "AddWallet") { category = Just "Wallet" }

toEvent (ModifyWallets (RemoveWallet _)) = Just $ (defaultEvent "RemoveWallet") { category = Just "Wallet" }

toEvent (ModifyWallets (ModifyBalance _ (SetBalance _ _ _))) = Just $ (defaultEvent "SetBalance") { category = Just "Wallet" }

toEvent (ActionDragAndDrop _ eventType _) = Just $ (defaultEvent (show eventType)) { category = Just "Action" }

toEvent EvaluateActions = Just $ (defaultEvent "EvaluateActions") { category = Just "Action" }

toEvent (ChangeSimulation subAction) = toActionEvent subAction

toEvent (ChainAction (FocusTx (Just _))) = Just $ (defaultEvent "BlockchainFocus") { category = Just "Transaction" }

toEvent (ChainAction (FocusTx Nothing)) = Nothing

toEvent (ChainAction (ClipboardAction (Clipboard.CopyToClipboard _))) = Just $ (defaultEvent "ClipboardAction") { category = Just "CopyToClipboard" }

toActionEvent :: SimulationAction -> Maybe Event
toActionEvent (PopulateAction _ _) = Just $ (defaultEvent "PopulateAction") { category = Just "Action" }

toActionEvent (ModifyActions (AddAction _)) = Just $ (defaultEvent "AddAction") { category = Just "Action" }

toActionEvent (ModifyActions (AddWaitAction _)) = Just $ (defaultEvent "AddWaitAction") { category = Just "Action" }

toActionEvent (ModifyActions (RemoveAction _)) = Just $ (defaultEvent "RemoveAction") { category = Just "Action" }

toActionEvent (ModifyActions (SetPayToWalletValue _ _)) = Just $ (defaultEvent "SetPayToWalletValue") { category = Just "Action" }

toActionEvent (ModifyActions (SetPayToWalletRecipient _ _)) = Just $ (defaultEvent "SetPayToWalletRecipient") { category = Just "Action" }

toActionEvent (ModifyActions (SetWaitTime _ _)) = Just $ (defaultEvent "SetWaitTime") { category = Just "Action" }

toActionEvent (ModifyActions (SetWaitUntilTime _ _)) = Just $ (defaultEvent "SetWaitUntilTime") { category = Just "Action" }

handleAction ::
  forall m.
  MonadState State m =>
  MonadClipboard m =>
  MonadAsk (SPSettings_ SPParams_) m =>
  MonadApp m =>
  MonadAnimate m State =>
  HAction -> m Unit
handleAction Mounted = pure unit

handleAction (EditorAction action) = editorHandleAction action

handleAction (ActionDragAndDrop index DragStart event) = do
  setDataTransferData event textPlain (show index)
  assign _actionDrag (Just index)

handleAction (ActionDragAndDrop _ DragEnd event) = assign _actionDrag Nothing

handleAction (ActionDragAndDrop _ DragEnter event) = do
  preventDefault event
  setDropEffect DataTransfer.Move event

handleAction (ActionDragAndDrop _ DragOver event) = do
  preventDefault event
  setDropEffect DataTransfer.Move event

handleAction (ActionDragAndDrop _ DragLeave event) = pure unit

handleAction (ActionDragAndDrop destination Drop event) = do
  use _actionDrag
    >>= case _ of
        Just source -> modifying (_simulations <<< _current <<< _simulationActions) (Array.move source destination)
        _ -> pure unit
  preventDefault event
  assign _actionDrag Nothing

-- We just ignore most Chartist events.
handleAction (HandleBalancesChartMessage _) = pure unit

handleAction CheckAuthStatus = do
  assign _authStatus Loading
  authResult <- getOauthStatus
  assign _authStatus authResult

handleAction (GistAction subEvent) = handleGistAction subEvent

handleAction (ChangeView view) = do
  assign _currentView view
  when (view == Transactions) resizeBalancesChart

handleAction EvaluateActions =
  void
    $ runMaybeT
    $ do
        evaluation <-
          MaybeT do
            contents <- editorGetContents
            simulation <- peruse (_simulations <<< _current)
            pure $ join $ toEvaluation <$> contents <*> simulation
        assign _evaluationResult Loading
        result <- lift $ postEvaluation evaluation
        assign _evaluationResult result
        -- If we got a successful result, switch tab.
        case result of
          Success (JsonEither (Left _)) -> pure unit
          _ -> replaceViewOnSuccess result Simulations Transactions
        pure unit

handleAction (LoadScript key) = do
  contractDemos <- use _contractDemos
  case StaticData.lookup key contractDemos of
    Nothing -> pure unit
    Just (ContractDemo { contractDemoEditorContents, contractDemoSimulations, contractDemoContext }) -> do
      editorSetContents contractDemoEditorContents (Just 1)
      saveBuffer (unwrap contractDemoEditorContents)
      assign _currentView Editor
      assign _simulations $ Cursor.fromArray contractDemoSimulations
      assign _compilationResult (Success <<< JsonEither <<< Right $ contractDemoContext)
      assign _evaluationResult NotAsked

handleAction AddSimulationSlot = do
  knownCurrencies <- getKnownCurrencies
  mSignatures <- peruse (_successfulCompilationResult <<< _functionSchema)
  case mSignatures of
    Just signatures ->
      modifying _simulations
        ( \simulations ->
            let
              count = Cursor.length simulations

              simulationName = "Simulation #" <> show (count + 1)
            in
              Cursor.snoc simulations
                (mkSimulation knownCurrencies simulationName)
        )
    Nothing -> pure unit

handleAction (SetSimulationSlot index) = modifying _simulations (Cursor.setIndex index)

handleAction (RemoveSimulationSlot index) = modifying _simulations (Cursor.deleteAt index)

handleAction (ModifyWallets action) = do
  knownCurrencies <- getKnownCurrencies
  modifying (_simulations <<< _current <<< _simulationWallets) (handleActionWalletEvent (mkSimulatorWallet knownCurrencies) action)

handleAction (ChangeSimulation subaction) = do
  knownCurrencies <- getKnownCurrencies
  let
    initialValue = mkInitialValue knownCurrencies 0
  modifying (_simulations <<< _current <<< _simulationActions) (handleSimulationAction initialValue subaction)

handleAction (ChainAction subaction) = do
  mAnnotatedBlockchain <-
    peruse (_evaluationResult <<< _Success <<< _JsonEither <<< _Right <<< _resultRollup <<< to AnnotatedBlockchain)
  let
    wrapper = case subaction of
      (FocusTx _) -> animate (_blockchainVisualisationState <<< _chainFocusAppearing)
      _ -> identity
  wrapper
    $ zoomStateT _blockchainVisualisationState
    $ Chain.handleAction subaction mAnnotatedBlockchain

handleAction CompileProgram = do
  mContents <- editorGetContents
  case mContents of
    Nothing -> pure unit
    Just contents -> do
      oldCompilationResult <- use _compilationResult
      assign _compilationResult Loading
      newCompilationResult <- postContract contents
      assign _compilationResult newCompilationResult
      -- If we got a successful result, switch tab.
      case newCompilationResult of
        Success (JsonEither (Left _)) -> pure unit
        _ -> replaceViewOnSuccess newCompilationResult Editor Simulations
      -- Update the error display.
      editorSetAnnotations
        $ case newCompilationResult of
            Success (JsonEither (Left errors)) -> toAnnotations errors
            _ -> []
      -- If we have a result with new signatures, we can only hold
      -- onto the old actions if the signatures still match. Any
      -- change means we'll have to clear out the existing simulation.
      -- Same thing for currencies.
      -- Potentially we could be smarter about this. But for now,
      -- let's at least be correct.
      let
        oldSignatures = preview (_details <<< _functionSchema) oldCompilationResult

        newSignatures = preview (_details <<< _functionSchema) newCompilationResult

        oldCurrencies = preview (_details <<< _knownCurrencies) oldCompilationResult

        newCurrencies = preview (_details <<< _knownCurrencies) newCompilationResult
      unless
        ( oldSignatures == newSignatures
            && oldCurrencies
            == newCurrencies
        )
        ( assign _simulations
            $ case newCurrencies of
                Just currencies -> Cursor.singleton $ mkSimulation currencies "Simulation 1"
                Nothing -> Cursor.empty
        )
      pure unit

handleSimulationAction ::
  Value ->
  SimulationAction ->
  Array (ContractCall FormArgument) ->
  Array (ContractCall FormArgument)
handleSimulationAction _ (ModifyActions actionEvent) = Schema.handleActionEvent actionEvent

handleSimulationAction initialValue (PopulateAction n event) = do
  over
    ( ix n
        <<< _CallEndpoint
        <<< _argumentValues
        <<< _FunctionSchema
        <<< _argument
    )
    $ Schema.handleFormEvent initialValue event

_details :: forall a. Traversal' (WebData (JsonEither InterpreterError (InterpreterResult a))) a
_details = _Success <<< _Newtype <<< _Right <<< _InterpreterResult <<< _result

handleGistAction :: forall m. MonadApp m => MonadState State m => GistAction -> m Unit
handleGistAction PublishGist = do
  void
    $ runMaybeT do
        mContents <- lift $ editorGetContents
        simulations <- use _simulations
        newGist <- hoistMaybe $ mkNewGist { source: mContents, simulations }
        mGist <- use _createGistResult
        assign _createGistResult Loading
        newResult <-
          lift
            $ case preview (_Success <<< gistId) mGist of
                Nothing -> postGist newGist
                Just existingGistId -> patchGistByGistId newGist existingGistId
        assign _createGistResult newResult
        gistId <- hoistMaybe $ preview (_Success <<< gistId <<< _GistId) newResult
        assign _gistUrl (Just gistId)

handleGistAction (SetGistUrl newGistUrl) = assign _gistUrl (Just newGistUrl)

handleGistAction LoadGist =
  void $ runExceptT
    $ do
        mGistId <- ExceptT (note "Gist Url not set." <$> use _gistUrl)
        eGistId <- except $ Gists.parseGistUrl mGistId
        --
        assign _createGistResult Loading
        aGist <- lift $ getGistByGistId eGistId
        assign _createGistResult aGist
        gist <- ExceptT $ pure $ toEither (Left "Gist not loaded.") $ lmap errorToString aGist
        --
        -- Load the source, if available.
        content <- noteT "Source not found in gist." $ preview (_Just <<< gistFileContent <<< _Just) (playgroundGistFile gist)
        lift $ editorSetContents (SourceCode content) (Just 1)
        lift $ saveBuffer content
        assign _simulations Cursor.empty
        assign _evaluationResult NotAsked
        --
        -- Load the simulation, if available.
        simulationString <- noteT "Simulation not found in gist." $ preview (_Just <<< gistFileContent <<< _Just) (simulationGistFile gist)
        simulations <- mapExceptT (pure <<< unwrap) $ withExceptT renderForeignErrors $ decodeJSON simulationString
        assign _simulations simulations
  where
  toEither :: forall e a. Either e a -> RemoteData e a -> Either e a
  toEither _ (Success a) = Right a

  toEither _ (Failure e) = Left e

  toEither x Loading = x

  toEither x NotAsked = x

handleActionWalletEvent :: (Int -> SimulatorWallet) -> WalletEvent -> Array SimulatorWallet -> Array SimulatorWallet
handleActionWalletEvent mkWallet AddWallet wallets =
  let
    maxWalletId = fromMaybe 0 $ maximumOf (traversed <<< _simulatorWalletWallet <<< _walletId) wallets

    newWallet = mkWallet (maxWalletId + 1)
  in
    Array.snoc wallets newWallet

handleActionWalletEvent _ (RemoveWallet index) wallets = fromMaybe wallets $ Array.deleteAt index wallets

handleActionWalletEvent _ (ModifyBalance walletIndex action) wallets =
  over
    (ix walletIndex <<< _simulatorWalletBalance)
    (Schema.handleValueEvent action)
    wallets

replaceViewOnSuccess :: forall m e a. MonadState State m => RemoteData e a -> View -> View -> m Unit
replaceViewOnSuccess result source target = do
  currentView <- use _currentView
  when (isSuccess result && currentView == source)
    (assign _currentView target)

------------------------------------------------------------
toAnnotations :: InterpreterError -> Array Annotation
toAnnotations (TimeoutError _) = []

toAnnotations (CompilationErrors errors) = catMaybes (toAnnotation <$> errors)

toAnnotation :: CompilationError -> Maybe Annotation
toAnnotation (RawError _) = Nothing

toAnnotation (CompilationError { row, column, text }) =
  Just
    { type: "error"
    , row: row - 1
    , column
    , text: String.joinWith "\n" text
    }
