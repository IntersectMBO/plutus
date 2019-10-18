module MainFrame
  ( mainFrame
  , eval
  , initialState
  ) where

import Types

import Ace.Halogen.Component (AceMessage(TextChanged))
import Ace.Types (Annotation)
import Analytics (Event, defaultEvent, trackEvent)
import Chain.Eval (eval) as Chain
import Chain.Types (AnnotatedBlockchain(..), ChainFocus(..))
import Control.Bind (bindFlipped)
import Control.Comonad (extract)
import Control.Monad.Except (runExcept)
import Control.Monad.Maybe.Trans (MaybeT(..), runMaybeT)
import Control.Monad.Reader.Class (class MonadAsk)
import Control.Monad.State.Class (class MonadState)
import Control.Monad.State.Extra (zoomStateT)
import Control.Monad.Trans.Class (lift)
import Cursor (_current)
import Cursor as Cursor
import Data.Array (catMaybes, (..))
import Data.Array (deleteAt, snoc) as Array
import Data.Array.Extra (move) as Array
import Data.Either (Either(..), note)
import Data.Generic.Rep.Eq (genericEq)
import Data.Json.JsonEither (JsonEither(..), _JsonEither)
import Data.Lens (_1, _2, _Just, _Right, assign, modifying, over, set, to, traversed, use)
import Data.Lens.Extra (peruse)
import Data.Lens.Fold (maximumOf, preview)
import Data.Lens.Index (ix)
import Data.Lens.Iso.Newtype (_Newtype)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe)
import Data.MediaType.Common (textPlain)
import Data.Ord (Ordering(..))
import Data.String as String
import Effect (Effect)
import Effect.Aff.Class (class MonadAff)
import Effect.Class (class MonadEffect, liftEffect)
import Foreign.Generic (decodeJSON)
import Gist (_GistId, gistFileContent, gistId)
import Gists as Gists
import Halogen (Component)
import Halogen as H
import Halogen.HTML (HTML)
import Halogen.Query (HalogenM)
import Language.Haskell.Interpreter (CompilationError(CompilationError, RawError), InterpreterError(CompilationErrors, TimeoutError), _InterpreterResult)
import Ledger.Value (Value)
import MonadApp (class MonadApp, editorGetContents, editorGotoLine, editorSetAnnotations, editorSetContents, getGistByGistId, getOauthStatus, patchGistByGistId, postContract, postEvaluation, postGist, preventDefault, readFileFromDragEvent, runHalogenApp, saveBuffer, setDataTransferData, setDropEffect)
import Network.RemoteData (RemoteData(..), _Success, isSuccess)
import Playground.Gists (mkNewGist, playgroundGistFile, simulationGistFile)
import Playground.Server (SPParams_)
import Playground.Types (KnownCurrency, SimulatorWallet(SimulatorWallet), _CompilationResult, _FunctionSchema)
import Prelude (type (~>), Unit, Void, bind, const, discard, flip, join, pure, show, unit, unless, when, ($), (&&), (+), (-), (<$>), (<*>), (<<<), (==), (>>=))
import Servant.PureScript.Settings (SPSettings_)
import StaticData as StaticData
import View as View
import Wallet.Emulator.Types (Wallet(Wallet))
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
  Component HTML Query Unit Void m
mainFrame =
  H.lifecycleParentComponent
    { initialState: const initialState
    , render: View.render
    , eval: evalWithAnalyticsTracking
    , receiver: const Nothing
    , initializer: Just $ H.action $ CheckAuthStatus
    , finalizer: Nothing
    }

evalWithAnalyticsTracking ::
  forall m.
  MonadEffect m =>
  MonadAsk (SPSettings_ SPParams_) m =>
  MonadAff m =>
  Query ~> HalogenM State Query ChildQuery ChildSlot Void m
evalWithAnalyticsTracking query = do
  liftEffect $ analyticsTracking query
  runHalogenApp $ eval query

analyticsTracking :: forall a. Query a -> Effect Unit
analyticsTracking query = do
  case toEvent query of
    Nothing -> pure unit
    Just event -> trackEvent event

-- | Here we decide which top-level queries to track as GA events, and
-- how to classify them.
toEvent :: forall a. Query a -> Maybe Event
toEvent (HandleEditorMessage _ _) = Nothing

toEvent (HandleDragEvent _ _) = Nothing

toEvent (HandleDropEvent _ _) = Just $ defaultEvent "DropScript"

toEvent (HandleBalancesChartMessage _ _) = Nothing

toEvent (CheckAuthStatus _) = Nothing

toEvent (PublishGist _) = Just $ (defaultEvent "Publish") { category = Just "Gist" }

toEvent (SetGistUrl _ _) = Nothing

toEvent (LoadGist _) = Just $ (defaultEvent "LoadGist") { category = Just "Gist" }

toEvent (ChangeView view _) = Just $ (defaultEvent "View") { label = Just $ show view }

toEvent (LoadScript script a) = Just $ (defaultEvent "LoadScript") { label = Just script }

toEvent (CompileProgram a) = Just $ defaultEvent "CompileProgram"

toEvent (ScrollTo _ _) = Nothing

toEvent (AddSimulationSlot _) = Just $ (defaultEvent "AddSimulationSlot") { category = Just "Simulation" }

toEvent (SetSimulationSlot _ _) = Just $ (defaultEvent "SetSimulationSlot") { category = Just "Simulation" }

toEvent (RemoveSimulationSlot _ _) = Just $ (defaultEvent "RemoveSimulationSlot") { category = Just "Simulation" }

toEvent (ModifyWallets AddWallet _) = Just $ (defaultEvent "AddWallet") { category = Just "Wallet" }

toEvent (ModifyWallets (RemoveWallet _) _) = Just $ (defaultEvent "RemoveWallet") { category = Just "Wallet" }

toEvent (ModifyWallets (ModifyBalance _ (SetBalance _ _ _)) _) = Just $ (defaultEvent "SetBalance") { category = Just "Wallet" }

toEvent (ModifyActions (AddAction _) _) = Just $ (defaultEvent "AddAction") { category = Just "Action" }

toEvent (ActionDragAndDrop _ eventType _ _) = Just $ (defaultEvent (show eventType)) { category = Just "Action" }

toEvent (ModifyActions (AddWaitAction _) _) = Just $ (defaultEvent "AddWaitAction") { category = Just "Action" }

toEvent (ModifyActions (RemoveAction _) _) = Just $ (defaultEvent "RemoveAction") { category = Just "Action" }

toEvent (ModifyActions (SetWaitTime _ _) _) = Just $ (defaultEvent "SetWaitTime") { category = Just "Action" }

toEvent (EvaluateActions _) = Just $ (defaultEvent "EvaluateActions") { category = Just "Action" }

toEvent (PopulateAction _ _ _) = Just $ (defaultEvent "PopulateAction") { category = Just "Action" }

toEvent (SetChainFocus (Just (FocusTx _)) _) = Just $ (defaultEvent "BlockchainFocus") { category = Just "Transaction" }

toEvent (SetChainFocus Nothing _) = Nothing

eval ::
  forall m.
  MonadState State m =>
  MonadAsk (SPSettings_ SPParams_) m =>
  MonadApp m =>
  Query ~> m
eval (HandleEditorMessage (TextChanged text) next) = do
  saveBuffer text
  pure next

eval (ActionDragAndDrop index DragStart event next) = do
  setDataTransferData event textPlain (show index)
  assign _actionDrag (Just index)
  pure next

eval (ActionDragAndDrop _ DragEnd event next) = do
  assign _actionDrag Nothing
  pure next

eval (ActionDragAndDrop _ DragEnter event next) = do
  preventDefault event
  setDropEffect DataTransfer.Move event
  pure next

eval (ActionDragAndDrop _ DragOver event next) = do
  preventDefault event
  setDropEffect DataTransfer.Move event
  pure next

eval (ActionDragAndDrop _ DragLeave event next) = do
  pure next

eval (ActionDragAndDrop destination Drop event next) = do
  use _actionDrag
    >>= case _ of
        Just source -> modifying (_simulations <<< _current <<< _actions) (Array.move source destination)
        _ -> pure unit
  preventDefault event
  assign _actionDrag Nothing
  pure next

eval (HandleDragEvent event next) = do
  preventDefault event
  pure next

eval (HandleDropEvent event next) = do
  preventDefault event
  contents <- readFileFromDragEvent event
  editorSetContents contents (Just 1)
  saveBuffer contents
  pure next

-- We just ignore most Chartist events.
eval (HandleBalancesChartMessage _ next) = pure next

eval (CheckAuthStatus next) = do
  assign _authStatus Loading
  authResult <- getOauthStatus
  assign _authStatus authResult
  pure next

eval (PublishGist next) = do
  mContents <- editorGetContents
  simulations <- use _simulations
  case mkNewGist { source: mContents, simulations } of
    Nothing -> pure next
    Just newGist -> do
      mGist <- use _createGistResult
      assign _createGistResult Loading
      newResult <- case preview (_Success <<< gistId) mGist of
        Nothing -> postGist newGist
        Just gistId -> patchGistByGistId newGist gistId
      assign _createGistResult newResult
      case preview (_Success <<< gistId <<< _GistId) newResult of
        Nothing -> pure unit
        Just gistId -> assign _gistUrl (Just gistId)
      pure next

eval (SetGistUrl newGistUrl next) = do
  assign _gistUrl (Just newGistUrl)
  pure next

eval (LoadGist next) = do
  eGistId <- (bindFlipped Gists.parseGistUrl <<< note "Gist Url not set.") <$> use _gistUrl
  case eGistId of
    Left err -> pure unit
    Right gistId -> do
      assign _createGistResult Loading
      aGist <- getGistByGistId gistId
      assign _createGistResult aGist
      case aGist of
        Success gist -> do
          -- Load the source, if available.
          case preview (_Just <<< gistFileContent <<< _Just) (playgroundGistFile gist) of
            Nothing -> pure unit
            Just content -> do
              editorSetContents content (Just 1)
              saveBuffer content
              assign _simulations Cursor.empty
              assign _evaluationResult NotAsked
          -- Load the simulation, if available.
          case preview (_Just <<< gistFileContent <<< _Just) (simulationGistFile gist) of
            Nothing -> pure unit
            Just simulationString -> do
              case runExcept (decodeJSON simulationString) of
                Left err -> pure unit
                Right simulations -> do
                  assign _simulations simulations
                  assign _evaluationResult NotAsked
        _ -> pure unit
  pure next

eval (ChangeView view next) = do
  assign _currentView view
  pure next

eval (LoadScript key next) = do
  case Map.lookup key StaticData.demoFiles of
    Nothing -> pure next
    Just contents -> do
      editorSetContents contents (Just 1)
      saveBuffer contents
      assign _currentView Editor
      assign _compilationResult NotAsked
      assign _evaluationResult NotAsked
      assign _simulations Cursor.empty
      pure next

eval (CompileProgram next) = do
  mContents <- editorGetContents
  case mContents of
    Nothing -> pure next
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
      pure next

eval (ScrollTo { row, column } next) = do
  editorGotoLine row (Just column)
  pure next

eval (ModifyActions actionEvent next) = do
  modifying (_simulations <<< _current <<< _actions) (evalActionEvent actionEvent)
  pure next

eval (EvaluateActions next) = do
  _ <-
    runMaybeT
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
  pure next

eval (AddSimulationSlot next) = do
  knownCurrencies <- getKnownCurrencies
  mSignatures <- peruse (_compilationResult <<< _Success <<< _Newtype <<< _Right <<< _InterpreterResult <<< _result <<< _CompilationResult <<< _functionSchema)
  case mSignatures of
    Just signatures -> modifying _simulations (flip Cursor.snoc (mkSimulation knownCurrencies signatures))
    Nothing -> pure unit
  pure next

eval (SetSimulationSlot index next) = do
  modifying _simulations (Cursor.setIndex index)
  pure next

eval (RemoveSimulationSlot index next) = do
  modifying _simulations (Cursor.deleteAt index)
  pure next

eval (ModifyWallets action next) = do
  knownCurrencies <- getKnownCurrencies
  modifying (_simulations <<< _current <<< _wallets) (evalWalletEvent (mkSimulatorWallet knownCurrencies) action)
  pure next

eval (PopulateAction n l event) = do
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
    (evalForm initialValue event)
  pure $ extract event

eval (SetChainFocus newFocus next) = do
  mAnnotatedBlockchain
    <- peruse (_evaluationResult <<< _Success <<< _JsonEither <<< _Right <<< _resultRollup <<< to AnnotatedBlockchain)

  zoomStateT _blockchainVisualisationState $ Chain.eval newFocus mAnnotatedBlockchain next

evalWalletEvent :: (Int -> SimulatorWallet) -> WalletEvent -> Array SimulatorWallet -> Array SimulatorWallet
evalWalletEvent mkWallet AddWallet wallets =
  let
    maxWalletId = fromMaybe 0 $ maximumOf (traversed <<< _simulatorWalletWallet <<< _walletId) wallets

    newWallet = mkWallet (maxWalletId + 1)
  in
    Array.snoc wallets newWallet

evalWalletEvent _ (RemoveWallet index) wallets = fromMaybe wallets $ Array.deleteAt index wallets

evalWalletEvent _ (ModifyBalance walletIndex action) wallets =
  over
    (ix walletIndex <<< _simulatorWalletBalance)
    (evalValueEvent action)
    wallets

evalValueEvent :: ValueEvent -> Value -> Value
evalValueEvent (SetBalance currencySymbol tokenName amount) = set (_value <<< ix currencySymbol <<< ix tokenName) amount

evalActionEvent :: ActionEvent -> Array Action -> Array Action
evalActionEvent (AddAction action) = flip Array.snoc action

evalActionEvent (AddWaitAction blocks) = flip Array.snoc (Wait { blocks })

evalActionEvent (RemoveAction index) = fromMaybe <*> Array.deleteAt index

evalActionEvent (SetWaitTime index time) = set (ix index <<< _Wait <<< _blocks) time

evalForm ::
  forall a.
  Value ->
  FormEvent a ->
  FormArgument ->
  FormArgument
evalForm initialValue = rec
  where
  evalField (SetIntField n) (FormInt _) = FormInt n

  evalField (SetBoolField n) (FormBool _) = FormBool n

  evalField (SetStringField s) (FormString _) = FormString (Just s)

  evalField (SetHexField s) (FormHex _) = FormHex (Just s)

  evalField (SetRadioField s) (FormRadio options _) = FormRadio options (Just s)

  evalField (SetValueField valueEvent) (FormValue value) = FormValue $ evalValueEvent valueEvent value

  evalField (SetSlotRangeField newInterval) arg@(FormSlotRange _) = FormSlotRange newInterval

  evalField _ arg = arg

  rec (SetField field subEvent) arg = evalField field arg

  rec (SetSubField 1 subEvent) (FormTuple fields) = FormTuple $ over (_Newtype <<< _1) (rec subEvent) fields

  rec (SetSubField 2 subEvent) (FormTuple fields) = FormTuple $ over (_Newtype <<< _2) (rec subEvent) fields

  rec (SetSubField 0 subEvent) (FormMaybe schema field) = FormMaybe schema $ over _Just (rec subEvent) field

  rec (SetSubField n subEvent) (FormArray schema fields) = FormArray schema $ over (ix n) (rec subEvent) fields

  rec (SetSubField n subEvent) s@(FormObject fields) = FormObject $ over (ix n <<< _Newtype <<< _2) (rec subEvent) fields

  rec (AddSubField _) (FormArray schema fields) =
    -- As the code stands, this is the only guarantee we get that every
    -- value in the array will conform to the schema: the fact that we
    -- create the 'empty' version from the same schema template.
    --
    -- Is more type safety than that possible? Probably.
    -- Is it worth the research effort? Perhaps. :thinking_face:
    FormArray schema $ Array.snoc fields (toArgument initialValue schema)

  rec (AddSubField _) arg = arg

  rec (RemoveSubField n subEvent) arg@(FormArray schema fields) = (FormArray schema (fromMaybe fields (Array.deleteAt n fields)))

  rec _ arg = arg

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
