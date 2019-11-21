module MainFrame
  ( mainFrame
  , handleAction
  , initialState
  ) where

import Types
import Ace.Halogen.Component (AceMessage(TextChanged))
import Ace.Types (Annotation)
import AjaxUtils (renderForeignErrors)
import Analytics (Event, defaultEvent, trackEvent)
import Chain.Eval as Chain
import Chain.Types (AnnotatedBlockchain(..), ChainFocus(..))
import Control.Monad.Except.Extra (noteT)
import Control.Monad.Except.Trans (ExceptT(..), except, mapExceptT, withExceptT, runExceptT)
import Control.Monad.Maybe.Extra (hoistMaybe)
import Control.Monad.Maybe.Trans (MaybeT(..), runMaybeT)
import Control.Monad.Reader.Class (class MonadAsk)
import Control.Monad.State.Class (class MonadState)
import Control.Monad.State.Extra (zoomStateT)
import Control.Monad.Trans.Class (lift)
import Cursor (_current)
import Cursor as Cursor
import Data.Array (catMaybes, (..))
import Data.Array (deleteAt, snoc) as Array
import Data.Array.Extra (move, lookup) as Array
import Data.Bifunctor (lmap)
import Data.Either (Either(..), note)
import Data.Functor.Fix (Fix(..))
import Data.Generic.Rep.Eq (genericEq)
import Data.Json.JsonEither (JsonEither(..), _JsonEither)
import Data.Lens (_2, _Just, _Right, assign, modifying, over, set, to, traversed, use)
import Data.Lens.Extra (peruse)
import Data.Lens.Fold (maximumOf, preview)
import Data.Lens.Index (ix)
import Data.Lens.Iso.Newtype (_Newtype)
import Data.Maybe (Maybe(..), fromMaybe)
import Data.MediaType.Common (textPlain)
import Data.Newtype (unwrap)
import Data.Ord (Ordering(..))
import Data.String as String
import Editor (EditorAction(..))
import Effect (Effect)
import Effect.Aff.Class (class MonadAff)
import Effect.Class (class MonadEffect, liftEffect)
import Foreign.Generic (decodeJSON)
import Gist (_GistId, gistFileContent, gistId)
import Gists (GistAction(..))
import Gists as Gists
import Halogen (Component)
import Halogen as H
import Halogen.HTML (HTML)
import Halogen.Query (HalogenM)
import Language.Haskell.Interpreter (CompilationError(CompilationError, RawError), InterpreterError(CompilationErrors, TimeoutError), _InterpreterResult)
import Ledger.Value (Value)
import Matryoshka (cata)
import MonadApp (class MonadApp, editorGetContents, editorGotoLine, editorSetAnnotations, editorSetContents, getGistByGistId, getOauthStatus, patchGistByGistId, postContract, postEvaluation, postGist, preventDefault, readFileFromDragEvent, runHalogenApp, saveBuffer, setDataTransferData, setDropEffect)
import Network.RemoteData (RemoteData(..), _Success, isSuccess)
import Playground.Gists (mkNewGist, playgroundGistFile, simulationGistFile)
import Playground.Server (SPParams_)
import Playground.Types (FormArgumentF(..), KnownCurrency, SimulatorWallet(SimulatorWallet), _CompilationResult, _FunctionSchema)
import Prelude (Unit, Void, bind, const, discard, flip, join, pure, show, unit, unless, void, when, ($), (&&), (+), (-), (<$>), (<*>), (<<<), (==), (>>=))
import Servant.PureScript.Ajax (errorToString)
import Servant.PureScript.Settings (SPSettings_)
import StaticData as StaticData
import View as View
import Wallet.Emulator.Wallet (Wallet(Wallet))
import Web.HTML.Event.DataTransfer as DataTransfer

mkSimulatorWallet :: Array KnownCurrency -> Int -> SimulatorWallet
mkSimulatorWallet currencies walletId =
  SimulatorWallet
    { simulatorWalletWallet: Wallet { getWallet: walletId }
    , simulatorWalletBalance: mkInitialValue currencies 10
    }

mkSimulation :: Array KnownCurrency -> Signatures -> Simulation
mkSimulation currencies signatures =
  Simulation
    { signatures
    , actions: []
    , wallets: mkSimulatorWallet currencies <$> 1 .. 2
    , currencies
    }

initialState :: State
initialState =
  State
    { currentView: Editor
    , compilationResult: NotAsked
    , simulations: Cursor.empty
    , actionDrag: Nothing
    , evaluationResult: NotAsked
    , authStatus: NotAsked
    , createGistResult: NotAsked
    , gistUrl: Nothing
    , blockchainVisualisationState:
      { chainFocus: Nothing
      , chainFocusAppearing: false
      , chainFocusAge: EQ
      }
    }

------------------------------------------------------------
mainFrame ::
  forall m.
  MonadAff m =>
  MonadAsk (SPSettings_ SPParams_) m =>
  Component HTML Query HAction Void m
mainFrame =
  H.mkComponent
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
handleActionWithAnalyticsTracking query = do
  liftEffect $ analyticsTracking query
  runHalogenApp $ handleAction query

analyticsTracking :: HAction -> Effect Unit
analyticsTracking query = do
  case toEvent query of
    Nothing -> pure unit
    Just event -> trackEvent event

-- | Here we decide which top-level queries to track as GA events, and
-- how to classify them.
toEvent :: HAction -> Maybe Event
toEvent Mounted = Just $ defaultEvent "Mounted"

toEvent (EditorAction (HandleEditorMessage _)) = Nothing

toEvent (EditorAction (HandleDragEvent _)) = Nothing

toEvent (EditorAction (HandleDropEvent _)) = Just $ defaultEvent "DropScript"

toEvent (EditorAction (LoadScript script)) = Just $ (defaultEvent "LoadScript") { label = Just script }

toEvent (EditorAction CompileProgram) = Just $ defaultEvent "CompileProgram"

toEvent (EditorAction (ScrollTo _)) = Nothing

toEvent (HandleBalancesChartMessage _) = Nothing

toEvent CheckAuthStatus = Nothing

toEvent (GistAction PublishGist) = Just $ (defaultEvent "Publish") { category = Just "Gist" }

toEvent (GistAction (SetGistUrl _)) = Nothing

toEvent (GistAction LoadGist) = Just $ (defaultEvent "LoadGist") { category = Just "Gist" }

toEvent (ChangeView view) = Just $ (defaultEvent "View") { label = Just $ show view }

toEvent AddSimulationSlot = Just $ (defaultEvent "AddSimulationSlot") { category = Just "Simulation" }

toEvent (SetSimulationSlot _) = Just $ (defaultEvent "SetSimulationSlot") { category = Just "Simulation" }

toEvent (RemoveSimulationSlot _) = Just $ (defaultEvent "RemoveSimulationSlot") { category = Just "Simulation" }

toEvent (ModifyWallets AddWallet) = Just $ (defaultEvent "AddWallet") { category = Just "Wallet" }

toEvent (ModifyWallets (RemoveWallet _)) = Just $ (defaultEvent "RemoveWallet") { category = Just "Wallet" }

toEvent (ModifyWallets (ModifyBalance _ (SetBalance _ _ _))) = Just $ (defaultEvent "SetBalance") { category = Just "Wallet" }

toEvent (ModifyActions (AddAction _)) = Just $ (defaultEvent "AddAction") { category = Just "Action" }

toEvent (ActionDragAndDrop _ eventType _) = Just $ (defaultEvent (show eventType)) { category = Just "Action" }

toEvent (ModifyActions (AddWaitAction _)) = Just $ (defaultEvent "AddWaitAction") { category = Just "Action" }

toEvent (ModifyActions (RemoveAction _)) = Just $ (defaultEvent "RemoveAction") { category = Just "Action" }

toEvent (ModifyActions (SetWaitTime _ _)) = Just $ (defaultEvent "SetWaitTime") { category = Just "Action" }

toEvent EvaluateActions = Just $ (defaultEvent "EvaluateActions") { category = Just "Action" }

toEvent (PopulateAction _ _ _) = Just $ (defaultEvent "PopulateAction") { category = Just "Action" }

toEvent (SetChainFocus (Just (FocusTx _))) = Just $ (defaultEvent "BlockchainFocus") { category = Just "Transaction" }

toEvent (SetChainFocus Nothing) = Nothing

handleAction ::
  forall m.
  MonadState State m =>
  MonadAsk (SPSettings_ SPParams_) m =>
  MonadApp m =>
  HAction -> m Unit
handleAction Mounted = pure unit

handleAction (EditorAction subEvent) = handleEditorAction subEvent

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
        Just source -> modifying (_simulations <<< _current <<< _actions) (Array.move source destination)
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

handleAction (ChangeView view) = assign _currentView view

handleAction (ModifyActions actionEvent) = modifying (_simulations <<< _current <<< _actions) (handleActionActionEvent actionEvent)

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

handleAction AddSimulationSlot = do
  knownCurrencies <- getKnownCurrencies
  mSignatures <- peruse (_compilationResult <<< _Success <<< _Newtype <<< _Right <<< _InterpreterResult <<< _result <<< _CompilationResult <<< _functionSchema)
  case mSignatures of
    Just signatures -> modifying _simulations (flip Cursor.snoc (mkSimulation knownCurrencies signatures))
    Nothing -> pure unit

handleAction (SetSimulationSlot index) = modifying _simulations (Cursor.setIndex index)

handleAction (RemoveSimulationSlot index) = modifying _simulations (Cursor.deleteAt index)

handleAction (ModifyWallets action) = do
  knownCurrencies <- getKnownCurrencies
  modifying (_simulations <<< _current <<< _wallets) (handleActionWalletEvent (mkSimulatorWallet knownCurrencies) action)

handleAction (PopulateAction n l event) = do
  knownCurrencies <- getKnownCurrencies
  let
    initialValue = mkInitialValue knownCurrencies 0
  modifying
    ( _simulations
        <<< _current
        <<< _actions
        <<< ix n
        <<< _Action
        <<< _functionSchema
        <<< _FunctionSchema
        <<< _argumentSchema
        <<< ix l
    )
    (handleActionForm initialValue event)

handleAction (SetChainFocus newFocus) = do
  mAnnotatedBlockchain <-
    peruse (_evaluationResult <<< _Success <<< _JsonEither <<< _Right <<< _resultRollup <<< to AnnotatedBlockchain)
  zoomStateT _blockchainVisualisationState $ Chain.handleAction newFocus mAnnotatedBlockchain

handleEditorAction :: forall m. MonadApp m => MonadState State m => EditorAction -> m Unit
handleEditorAction (HandleEditorMessage (TextChanged text)) = saveBuffer text

handleEditorAction (HandleDragEvent event) = preventDefault event

handleEditorAction (HandleDropEvent event) = do
  preventDefault event
  contents <- readFileFromDragEvent event
  editorSetContents contents (Just 1)
  saveBuffer contents

handleEditorAction (LoadScript key) = do
  case Array.lookup key StaticData.demoFiles of
    Nothing -> pure unit
    Just contents -> do
      editorSetContents contents (Just 1)
      saveBuffer contents
      assign _currentView Editor
      assign _compilationResult NotAsked
      assign _evaluationResult NotAsked
      assign _simulations Cursor.empty

handleEditorAction CompileProgram = do
  mContents <- editorGetContents
  case mContents of
    Nothing -> pure unit
    Just contents -> do
      assign _compilationResult Loading
      result <- postContract contents
      assign _compilationResult result
      -- If we got a successful result, switch tab.
      case result of
        Success (JsonEither (Left _)) -> pure unit
        _ -> replaceViewOnSuccess result Editor Simulations
      -- Update the error display.
      editorSetAnnotations
        $ case result of
            Success (JsonEither (Left errors)) -> toAnnotations errors
            _ -> []
      -- If we have a result with new signatures, we can only hold
      -- onto the old actions if the signatures still match. Any
      -- change means we'll have to clear out the existing simulation.
      -- Same thing for currencies.
      -- Potentially we could be smarter about this. But for now,
      -- let's at least be correct.
      case preview (_Success <<< _Newtype <<< _Right <<< _InterpreterResult <<< _result <<< _CompilationResult) result of
        Just { functionSchema: newSignatures, knownCurrencies: newCurrencies } -> do
          oldSimulation <- peruse (_simulations <<< _current <<< _Newtype)
          unless
            ( ((_.signatures <$> oldSimulation) `genericEq` Just newSignatures)
                && ((_.currencies <$> oldSimulation) `genericEq` Just newCurrencies)
            )
            (assign _simulations $ Cursor.singleton $ mkSimulation newCurrencies newSignatures)
        _ -> pure unit

handleEditorAction (ScrollTo { row, column }) = editorGotoLine row (Just column)

handleGistAction :: forall m. MonadApp m => MonadState State m => GistAction -> m Unit
handleGistAction PublishGist = do
  void $ runMaybeT
    $ do
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
        lift $ editorSetContents content (Just 1)
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
    (handleActionValueEvent action)
    wallets

handleActionValueEvent :: ValueEvent -> Value -> Value
handleActionValueEvent (SetBalance currencySymbol tokenName amount) = set (_value <<< ix currencySymbol <<< ix tokenName) amount

handleActionActionEvent :: ActionEvent -> Array Action -> Array Action
handleActionActionEvent (AddAction action) = flip Array.snoc action

handleActionActionEvent (AddWaitAction blocks) = flip Array.snoc (Wait { blocks })

handleActionActionEvent (RemoveAction index) = fromMaybe <*> Array.deleteAt index

handleActionActionEvent (SetWaitTime index time) = set (ix index <<< _Wait <<< _blocks) time

handleActionForm ::
  Value ->
  FormEvent ->
  FormArgument ->
  FormArgument
handleActionForm initialValue event = cata (Fix <<< algebra event)
  where
  algebra (SetField (SetIntField n)) (FormIntF _) = FormIntF n

  algebra (SetField (SetBoolField n)) (FormBoolF _) = FormBoolF n

  algebra (SetField (SetStringField s)) (FormStringF _) = FormStringF (Just s)

  algebra (SetField (SetHexField s)) (FormHexF _) = FormHexF (Just s)

  algebra (SetField (SetRadioField s)) (FormRadioF options _) = FormRadioF options (Just s)

  algebra (SetField (SetValueField valueEvent)) (FormValueF value) = FormValueF $ handleActionValueEvent valueEvent value

  algebra (SetField (SetSlotRangeField newInterval)) arg@(FormSlotRangeF _) = FormSlotRangeF newInterval

  algebra (SetSubField 1 subEvent) (FormTupleF field1 field2) = FormTupleF (handleActionForm initialValue subEvent field1) field2

  algebra (SetSubField 1 subEvent) (FormTupleF field1 field2) = FormTupleF field1 (handleActionForm initialValue subEvent field2)

  algebra (SetSubField 0 subEvent) (FormMaybeF schema field) = FormMaybeF schema $ over _Just (handleActionForm initialValue subEvent) field

  algebra (SetSubField n subEvent) (FormArrayF schema fields) = FormArrayF schema $ over (ix n) (handleActionForm initialValue subEvent) fields

  algebra (SetSubField n subEvent) s@(FormObjectF fields) = FormObjectF $ over (ix n <<< _Newtype <<< _2) (handleActionForm initialValue subEvent) fields

  -- As the code stands, this is the only guarantee we get that every
  -- value in the array will conform to the schema: the fact that we
  -- create the 'empty' version from the same schema template.
  -- Is more type safety than that possible? Probably.
  -- Is it worth the research effort? Perhaps. :thinking_face:
  algebra AddSubField (FormArrayF schema fields) = FormArrayF schema $ Array.snoc fields (toArgument initialValue schema)

  algebra AddSubField arg = arg

  algebra (RemoveSubField n) arg@(FormArrayF schema fields) = (FormArrayF schema (fromMaybe fields (Array.deleteAt n fields)))

  algebra _ arg = arg

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
