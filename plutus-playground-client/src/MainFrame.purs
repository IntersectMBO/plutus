module MainFrame
  ( mkMainFrame
  , handleAction
  , mkInitialState
  ) where

import Prelude
import AjaxUtils (ajaxErrorRefLabel, renderForeignErrors, AjaxErrorPaneAction(CloseErrorPane))
import Analytics (Event, defaultEvent, trackEvent)
import Animation (class MonadAnimate, animate)
import Chain.State (handleAction) as Chain
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
import Data.BigInteger (BigInteger)
import Data.BigInteger as BigInteger
import Data.Either (Either(..), note)
import Data.Lens (Traversal', _Right, assign, modifying, over, to, traversed, use, view)
import Data.Lens.Extra (peruse)
import Data.Lens.Fold (maximumOf, preview)
import Data.Lens.Index (ix)
import Data.Maybe (Maybe(..), fromMaybe)
import Data.MediaType.Common (textPlain)
import Data.Newtype (unwrap)
import Data.String as String
import Editor.State (initialState) as Editor
import Editor.Types (_currentCodeIsCompiled, _feedbackPaneMinimised, _lastCompiledCode)
import Editor.Types (Action(..), State) as Editor
import Effect (Effect)
import Effect.Aff.Class (class MonadAff)
import Effect.Class (class MonadEffect, liftEffect)
import Effect.Exception (Error, error)
import Foreign.Generic (decodeJSON)
import Gist (_GistId, gistId)
import Gists.Types (GistAction(..))
import Gists.Types as Gists
import Halogen (Component, hoist)
import Halogen as H
import Halogen.HTML (HTML)
import Halogen.Query (HalogenM)
import Language.Haskell.Interpreter (CompilationError(..), InterpreterError(..), InterpreterResult, SourceCode(..), _InterpreterResult)
import Ledger.Value (Value)
import Monaco (IMarkerData, markerSeverity)
import MonadApp (class MonadApp, editorGetContents, editorHandleAction, editorSetAnnotations, editorSetContents, getGistByGistId, getOauthStatus, patchGistByGistId, postContract, postEvaluation, postGist, preventDefault, resizeBalancesChart, resizeEditor, runHalogenApp, saveBuffer, scrollIntoView, setDataTransferData, setDropEffect)
import Network.RemoteData (RemoteData(..), _Success, isSuccess)
import Playground.Gists (mkNewGist, playgroundGistFile, simulationGistFile)
import Playground.Server (SPParams_(..))
import Playground.Types (ContractCall, ContractDemo(..), KnownCurrency, Simulation(..), SimulatorWallet(..), _CallEndpoint, _FunctionSchema)
import Schema.Types (ActionEvent(..), FormArgument, SimulationAction(..), mkInitialValue)
import Schema.Types as Schema
import Servant.PureScript.Ajax (errorToString)
import Servant.PureScript.Settings (SPSettings_, defaultSettings)
import Simulation (simulatorTitleRefLabel, simulationsErrorRefLabel)
import StaticData (mkContractDemos)
import StaticData as StaticData
import Types (ChildSlots, DragAndDropEventType(..), HAction(..), Query, State(..), View(..), WalletEvent(..), WebData, _actionDrag, _authStatus, _blockchainVisualisationState, _compilationResult, _contractDemos, _createGistResult, _currentDemoName, _currentView, _demoFilesMenuOpen, _editorState, _evaluationResult, _functionSchema, _gistErrorPaneVisible, _gistUrl, _lastEvaluatedSimulation, _knownCurrencies, _result, _resultRollup, _simulationActions, _simulationWallets, _simulations, _simulatorWalletBalance, _simulatorWalletWallet, _successfulCompilationResult, _walletId, getKnownCurrencies, toEvaluation)
import Validation (_argumentValues, _argument)
import ValueEditor (ValueEvent(..))
import View as View
import Wallet.Emulator.Wallet (Wallet(Wallet))
import Web.HTML.Event.DataTransfer as DataTransfer

mkSimulatorWallet :: Array KnownCurrency -> BigInteger -> SimulatorWallet
mkSimulatorWallet currencies walletId =
  SimulatorWallet
    { simulatorWalletWallet: Wallet { getWallet: walletId }
    , simulatorWalletBalance: mkInitialValue currencies (BigInteger.fromInt 10)
    }

mkSimulation :: Array KnownCurrency -> String -> Simulation
mkSimulation simulationCurrencies simulationName =
  Simulation
    { simulationName
    , simulationActions: []
    , simulationWallets: mkSimulatorWallet simulationCurrencies <<< BigInteger.fromInt <$> 1 .. 2
    }

mkInitialState :: forall m. MonadThrow Error m => Editor.State -> m State
mkInitialState editorState = do
  contractDemos <- mapError (\e -> error $ "Could not load demo scripts. Parsing errors: " <> show e) mkContractDemos
  pure
    $ State
        { demoFilesMenuOpen: false
        , currentView: Editor
        , editorState
        , contractDemos
        , currentDemoName: Nothing
        , compilationResult: NotAsked
        , simulations: Cursor.empty
        , actionDrag: Nothing
        , evaluationResult: NotAsked
        , lastEvaluatedSimulation: Nothing
        , authStatus: NotAsked
        , createGistResult: NotAsked
        , gistUrl: Nothing
        , gistErrorPaneVisible: true
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
  editorState <- Editor.initialState
  initialState <- mkInitialState editorState
  pure $ hoist (flip runReaderT ajaxSettings)
    $ H.mkComponent
        { initialState: const initialState
        , render: View.render
        , eval:
            H.mkEval
              { handleAction: handleActionWithAnalyticsTracking
              , handleQuery: const $ pure Nothing
              , initialize: Just Init
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
toEvent Init = Nothing

toEvent Mounted = Just $ defaultEvent "Mounted"

toEvent (EditorAction (Editor.HandleDropEvent _)) = Just $ defaultEvent "DropScript"

toEvent (EditorAction action) = Just $ (defaultEvent "ConfigureEditor")

toEvent CompileProgram = Just $ defaultEvent "CompileProgram"

toEvent (HandleBalancesChartMessage _) = Nothing

toEvent CheckAuthStatus = Nothing

toEvent (GistAction PublishGist) = Just $ (defaultEvent "Publish") { category = Just "Gist" }

toEvent (GistAction (SetGistUrl _)) = Nothing

toEvent (GistAction LoadGist) = Just $ (defaultEvent "LoadGist") { category = Just "Gist" }

toEvent (GistAction (AjaxErrorPaneAction _)) = Nothing

toEvent (ToggleDemoFilesMenu) = Just $ (defaultEvent "ToggleDemoFilesMenu")

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
handleAction Init = do
  handleAction CheckAuthStatus
  editorHandleAction $ Editor.Init

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

handleAction ToggleDemoFilesMenu = do
  modifying _demoFilesMenuOpen not

handleAction (ChangeView view) = do
  assign _currentView view
  when (view == Editor) resizeEditor
  when (view == Transactions) resizeBalancesChart

handleAction EvaluateActions =
  void
    $ runMaybeT
    $ do
        simulation <- peruse (_simulations <<< _current)
        evaluation <-
          MaybeT do
            contents <- editorGetContents
            pure $ join $ toEvaluation <$> contents <*> simulation
        assign _evaluationResult Loading
        result <- lift $ postEvaluation evaluation
        assign _evaluationResult result
        case result of
          Success (Right _) -> do
            -- on successful evaluation, update last evaluated simulation and show transactions
            updateSimulationOnSuccess result simulation
            replaceViewOnSuccess result Simulations Transactions
            lift $ scrollIntoView simulatorTitleRefLabel
          Success (Left _) -> do
            -- on failed evaluation, scroll the error pane into view
            lift $ scrollIntoView simulationsErrorRefLabel
          Failure _ -> do
            -- on failed response, scroll the ajax error pane into view
            lift $ scrollIntoView ajaxErrorRefLabel
          _ -> pure unit
        pure unit

handleAction (LoadScript key) = do
  contractDemos <- use _contractDemos
  case StaticData.lookup key contractDemos of
    Nothing -> pure unit
    Just (ContractDemo { contractDemoName, contractDemoEditorContents, contractDemoSimulations, contractDemoContext }) -> do
      editorSetContents contractDemoEditorContents (Just 1)
      saveBuffer (unwrap contractDemoEditorContents)
      assign _demoFilesMenuOpen false
      assign _currentView Editor
      assign _currentDemoName (Just contractDemoName)
      assign _simulations $ Cursor.fromArray contractDemoSimulations
      assign (_editorState <<< _lastCompiledCode) (Just contractDemoEditorContents)
      assign (_editorState <<< _currentCodeIsCompiled) true
      assign _compilationResult (Success <<< Right $ contractDemoContext)
      assign _evaluationResult NotAsked
      assign _createGistResult NotAsked

handleAction AddSimulationSlot = do
  knownCurrencies <- getKnownCurrencies
  mSignatures <- peruse (_successfulCompilationResult <<< _functionSchema)
  case mSignatures of
    Just signatures ->
      modifying _simulations
        ( \simulations ->
            let
              count = Cursor.length simulations

              simulationName = "Simulation " <> show (count + 1)
            in
              Cursor.snoc simulations
                (mkSimulation knownCurrencies simulationName)
        )
    Nothing -> pure unit
  -- The following is a temporary fudge to avoid weird behaviour if you're in
  -- the transaction view; in due course the model should be changed to include
  -- separate transactions for each simulation
  assign _currentView Simulations

handleAction (SetSimulationSlot index) = do
  modifying _simulations (Cursor.setIndex index)
  -- The same temporary fudge used above
  assign _currentView Simulations

handleAction (RemoveSimulationSlot index) = do
  -- The same temporary fudge used above (but only if the current simulation is being removed)
  simulations <- use _simulations
  if (Cursor.getIndex simulations) == index then
    assign _currentView Simulations
  else
    pure unit
  modifying _simulations (Cursor.deleteAt index)

handleAction (ModifyWallets action) = do
  knownCurrencies <- getKnownCurrencies
  modifying (_simulations <<< _current <<< _simulationWallets) (handleActionWalletEvent (mkSimulatorWallet knownCurrencies) action)

handleAction (ChangeSimulation subaction) = do
  knownCurrencies <- getKnownCurrencies
  let
    initialValue = mkInitialValue knownCurrencies zero
  modifying (_simulations <<< _current <<< _simulationActions) (handleSimulationAction initialValue subaction)

handleAction (ChainAction subaction) = do
  mAnnotatedBlockchain <-
    peruse (_evaluationResult <<< _Success <<< _Right <<< _resultRollup <<< to AnnotatedBlockchain)
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
      assign (_editorState <<< _feedbackPaneMinimised) false
      newCompilationResult <- postContract contents
      assign _compilationResult newCompilationResult
      -- If we got a successful result, update lastCompiledCode and switch tab.
      case newCompilationResult of
        Success (Left _) -> pure unit
        _ -> do
          -- next line commented out for now - I don't think we're doing this any more
          -- replaceViewOnSuccess newCompilationResult Editor Simulations
          updateCodeOnSuccess newCompilationResult (Just contents)
      -- Update the error display.
      editorSetAnnotations
        $ case newCompilationResult of
            Success (Left errors) -> toAnnotations errors
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

_details :: forall a. Traversal' (WebData (Either InterpreterError (InterpreterResult a))) a
_details = _Success <<< _Right <<< _InterpreterResult <<< _result

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
        updateViewOnSuccess newResult Editor
        clearCurrentDemoNameOnSuccess newResult

handleGistAction (SetGistUrl newGistUrl) = assign _gistUrl (Just newGistUrl)

handleGistAction LoadGist =
  void $ runExceptT
    $ do
        mGistId <- ExceptT (note "Gist Url not set." <$> use _gistUrl)
        eGistId <- except $ Gists.parseGistUrl mGistId
        --
        assign _createGistResult Loading
        assign _gistErrorPaneVisible true
        aGist <- lift $ getGistByGistId eGistId
        assign _createGistResult aGist
        updateViewOnSuccess aGist Editor
        clearCurrentDemoNameOnSuccess aGist
        gist <- ExceptT $ pure $ toEither (Left "Gist not loaded.") $ lmap errorToString aGist
        --
        -- Load the source, if available.
        content <- noteT "Source not found in gist." $ view playgroundGistFile gist
        lift $ editorSetContents (SourceCode content) (Just 1)
        lift $ saveBuffer content
        assign _simulations Cursor.empty
        assign _evaluationResult NotAsked
        --
        -- Load the simulation, if available.
        simulationString <- noteT "Simulation not found in gist." $ view simulationGistFile gist
        simulations <- mapExceptT (pure <<< unwrap) $ withExceptT renderForeignErrors $ decodeJSON simulationString
        assign _simulations simulations
  where
  toEither :: forall e a. Either e a -> RemoteData e a -> Either e a
  toEither _ (Success a) = Right a

  toEither _ (Failure e) = Left e

  toEither x Loading = x

  toEither x NotAsked = x

handleGistAction (AjaxErrorPaneAction CloseErrorPane) = assign _gistErrorPaneVisible false

handleActionWalletEvent :: (BigInteger -> SimulatorWallet) -> WalletEvent -> Array SimulatorWallet -> Array SimulatorWallet
handleActionWalletEvent mkWallet AddWallet wallets =
  let
    maxWalletId = fromMaybe zero $ maximumOf (traversed <<< _simulatorWalletWallet <<< _walletId) wallets

    newWallet = mkWallet (add one maxWalletId)
  in
    Array.snoc wallets newWallet

handleActionWalletEvent _ (RemoveWallet index) wallets = fromMaybe wallets $ Array.deleteAt index wallets

handleActionWalletEvent _ (ModifyBalance walletIndex action) wallets =
  over
    (ix walletIndex <<< _simulatorWalletBalance)
    (Schema.handleValueEvent action)
    wallets

updateSimulationOnSuccess :: forall m e a. MonadState State m => RemoteData e a -> Maybe Simulation -> m Unit
updateSimulationOnSuccess result simulation = do
  when (isSuccess result)
    (assign _lastEvaluatedSimulation simulation)

updateCodeOnSuccess :: forall m e a. MonadState State m => RemoteData e a -> Maybe SourceCode -> m Unit
updateCodeOnSuccess result code = do
  when (isSuccess result) do
    assign (_editorState <<< _lastCompiledCode) code
    assign (_editorState <<< _currentCodeIsCompiled) true

updateViewOnSuccess :: forall m e a. MonadState State m => RemoteData e a -> View -> m Unit
updateViewOnSuccess result target = do
  when (isSuccess result)
    (assign _currentView target)

replaceViewOnSuccess :: forall m e a. MonadState State m => RemoteData e a -> View -> View -> m Unit
replaceViewOnSuccess result source target = do
  currentView <- use _currentView
  when (isSuccess result && currentView == source)
    (assign _currentView target)

clearCurrentDemoNameOnSuccess :: forall m e a. MonadState State m => RemoteData e a -> m Unit
clearCurrentDemoNameOnSuccess result = do
  when (isSuccess result)
    (assign _currentDemoName Nothing)

------------------------------------------------------------
toAnnotations :: InterpreterError -> Array IMarkerData
toAnnotations (TimeoutError _) = []

toAnnotations (CompilationErrors errors) = catMaybes (toAnnotation <$> errors)

toAnnotation :: CompilationError -> Maybe IMarkerData
toAnnotation (RawError _) = Nothing

toAnnotation (CompilationError { row, column, text }) =
  Just
    { severity: markerSeverity "Error"
    , message: String.joinWith "\\n" text
    , startLineNumber: row
    , startColumn: column
    , endLineNumber: row
    , endColumn: column
    , code: mempty
    , source: mempty
    }
