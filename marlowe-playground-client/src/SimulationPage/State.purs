module SimulationPage.State where

import Control.Alternative (map, void, when, (<*>), (<|>))
import Control.Monad.Except (ExceptT, runExceptT, runExcept)
import Control.Monad.Reader (runReaderT)
import Data.Array (delete, filter, snoc)
import Data.Array as Array
import Data.BigInteger (BigInteger, fromString)
import Data.Decimal (truncated, fromNumber)
import Data.Decimal as Decimal
import Data.Either (Either(..), hush)
import Data.EuclideanRing ((*))
import Data.Lens (assign, modifying, over, preview, set, to, use)
import Data.Lens.Extra (peruse)
import Data.Lens.Index (ix)
import Data.Lens.NonEmptyList (_Head)
import Data.List.NonEmpty as NEL
import Data.List.Types (List(..), NonEmptyList)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe)
import Data.NonEmptyList.Extra (tailIfNotEmpty)
import Data.RawJson (RawJson(..))
import Data.String (codePointFromChar)
import Data.String as String
import Data.Traversable (for_, traverse)
import Data.Tuple (Tuple(..))
import Effect.Aff.Class (class MonadAff, liftAff)
import Effect.Class (class MonadEffect, liftEffect)
import Effect.Console (log)
import FileEvents (readFileFromDragEvent)
import FileEvents as FileEvents
import Foreign.Generic (ForeignError, decode)
import Foreign.JSON (parseJSON)
import Halogen (HalogenM, get, modify_, query)
import Halogen.Monaco (Message(..), Query(..)) as Monaco
import LocalStorage as LocalStorage
import MainFrame.Types (ChildSlots, _hasUnsavedChanges', _marloweEditorSlot)
import Marlowe (SPParams_)
import Marlowe as Server
import Marlowe.Holes (fromTerm)
import Marlowe.Linter as Linter
import Marlowe.Monaco (updateAdditionalContext)
import Marlowe.Monaco as MM
import Marlowe.Parser (parseContract)
import Marlowe.Semantics (ChoiceId(..), Input(..), Party(..), inBounds)
import Marlowe.Symbolic.Types.Request as MSReq
import Monaco (IMarker, isError, isWarning)
import Network.RemoteData (RemoteData(..))
import Network.RemoteData as RemoteData
import Prelude (Unit, Void, bind, discard, flip, identity, mempty, pure, show, unit, zero, ($), (-), (/=), (<), (<$>), (<<<), (<>), (=<<), (==), (>=))
import Reachability (areContractAndStateTheOnesAnalysed, getUnreachableContracts, startReachabilityAnalysis)
import Servant.PureScript.Ajax (AjaxError, errorToString)
import Servant.PureScript.Settings (SPSettings_)
import Simulator (applyInput, getAsMuchStateAsPossible, inFuture, moveToSignificantSlot, moveToSlot, nextSignificantSlot, updateContractInState, updateMarloweState)
import SimulationPage.Types (Action(..), ActionInput(..), ActionInputId(..), AnalysisState(..), ExecutionState(..), Parties(..), State, WebData, _SimulationNotStarted, _SimulationRunning, _analysisState, _bottomPanelView, _currentContract, _currentMarloweState, _editorErrors, _editorKeybindings, _editorWarnings, _executionState, _helpContext, _initialSlot, _marloweState, _moveToAction, _oldContract, _pendingInputs, _possibleActions, _selectedHole, _showBottomPanel, _showErrorDetail, _showRightPanel, emptyExecutionStateWithSlot, emptyMarloweState, mapPartiesActionInput)
import StaticData (marloweBufferLocalStorageKey)
import StaticData as StaticData
import Text.Pretty (genericPretty, pretty)
import Web.DOM.Document as D
import Web.DOM.Element (setScrollTop)
import Web.DOM.Element as E
import Web.DOM.HTMLCollection as WC
import Web.HTML as Web
import Web.HTML.HTMLDocument (toDocument)
import Web.HTML.Window as W

handleAction ::
  forall m.
  MonadEffect m =>
  MonadAff m =>
  SPSettings_ SPParams_ -> Action -> HalogenM State Action ChildSlots Void m Unit
handleAction settings Init = do
  editorSetTheme
  setOraclePrice settings

handleAction settings (HandleEditorMessage (Monaco.TextChanged "")) = do
  assign _marloweState $ NEL.singleton emptyMarloweState
  assign _oldContract Nothing
  updateContractInState ""

handleAction settings (HandleEditorMessage (Monaco.TextChanged text)) = do
  modify_
    ( set _selectedHole Nothing
        <<< set _hasUnsavedChanges' true
    )
  liftEffect $ LocalStorage.setItem marloweBufferLocalStorageKey text
  updateContractInState text
  analysisState <- use _analysisState
  currState <- getAsMuchStateAsPossible
  let
    parsedContract = parseContract text

    maybeContract = fromTerm =<< hush parsedContract

    reachabilityResultsValid = areContractAndStateTheOnesAnalysed analysisState maybeContract currState

    unreachableContracts = if reachabilityResultsValid then getUnreachableContracts analysisState else Nil

    (Tuple markerData additionalContext) = Linter.markers unreachableContracts parsedContract
  markers <- query _marloweEditorSlot unit (Monaco.SetModelMarkers markerData identity)
  void $ traverse editorSetMarkers markers
  objects <- query _marloweEditorSlot unit (Monaco.GetObjects identity)
  case objects of
    Just { codeActionProvider: Just caProvider, completionItemProvider: Just ciProvider } -> pure $ updateAdditionalContext caProvider ciProvider additionalContext
    _ -> pure unit

handleAction _ (HandleDragEvent event) = liftEffect $ FileEvents.preventDefault event

handleAction settings (HandleDropEvent event) = do
  liftEffect $ FileEvents.preventDefault event
  contents <- liftAff $ readFileFromDragEvent event
  void $ editorSetValue contents
  updateContractInState contents
  setOraclePrice settings

handleAction _ (MoveToPosition lineNumber column) = do
  void $ query _marloweEditorSlot unit (Monaco.SetPosition { column, lineNumber } unit)

handleAction _ (SelectEditorKeyBindings bindings) = do
  assign _editorKeybindings bindings
  void $ query _marloweEditorSlot unit (Monaco.SetKeyBindings bindings unit)

handleAction settings (LoadScript key) = do
  for_ (preview (ix key) StaticData.marloweContracts) \contents -> do
    let
      prettyContents = case parseContract contents of
        Right pcon -> show $ pretty pcon
        Left _ -> contents
    editorSetValue prettyContents
    liftEffect $ LocalStorage.setItem marloweBufferLocalStorageKey prettyContents
    updateContractInState prettyContents
    resetContract
    setOraclePrice settings

handleAction settings (SetEditorText contents) = do
  editorSetValue contents
  updateContractInState contents

handleAction settings (SetInitialSlot initialSlot) = do
  assign (_currentMarloweState <<< _executionState <<< _SimulationNotStarted <<< _initialSlot) initialSlot
  setOraclePrice settings

handleAction settings StartSimulation = do
  maybeInitialSlot <- peruse (_currentMarloweState <<< _executionState <<< _SimulationNotStarted <<< _initialSlot)
  for_ maybeInitialSlot \initialSlot -> do
    saveInitialState
    assign (_currentMarloweState <<< _executionState) (emptyExecutionStateWithSlot initialSlot)
    moveToSignificantSlot initialSlot
    mCurrContract <- use _currentContract
    case mCurrContract of
      Just currContract -> do
        editorSetValue (show $ genericPretty currContract)
        setOraclePrice settings
      Nothing -> pure unit

handleAction settings (MoveSlot slot) = do
  inTheFuture <- inFuture <$> get <*> pure slot
  significantSlot <- use (_marloweState <<< _Head <<< to nextSignificantSlot)
  when inTheFuture do
    saveInitialState
    if slot >= (fromMaybe zero significantSlot) then
      moveToSignificantSlot slot
    else
      moveToSlot slot
    mCurrContract <- use _currentContract
    case mCurrContract of
      Just currContract -> do
        editorSetValue (show $ genericPretty currContract)
        setOraclePrice settings
      Nothing -> pure unit

handleAction settings (SetSlot slot) = do
  assign (_currentMarloweState <<< _executionState <<< _SimulationRunning <<< _possibleActions <<< _moveToAction) (Just $ MoveToSlot slot)
  setOraclePrice settings

handleAction settings (AddInput input bounds) = do
  when validInput do
    saveInitialState
    applyInput ((flip snoc) input)
    mCurrContract <- use _currentContract
    case mCurrContract of
      Just currContract -> do
        editorSetValue (show $ genericPretty currContract)
        setOraclePrice settings
      Nothing -> pure unit
  where
  validInput = case input of
    (IChoice _ chosenNum) -> inBounds chosenNum bounds
    _ -> true

handleAction settings (RemoveInput input) = do
  updateMarloweState (over (_executionState <<< _SimulationRunning <<< _pendingInputs) (delete input))
  currContract <- editorGetValue
  case currContract of
    Nothing -> pure unit
    Just contract -> do
      updateContractInState contract
      setOraclePrice settings

handleAction _ (SetChoice choiceId chosenNum) = updateMarloweState (over (_executionState <<< _SimulationRunning <<< _possibleActions) (mapPartiesActionInput (updateChoice choiceId)))
  where
  updateChoice :: ChoiceId -> ActionInput -> ActionInput
  updateChoice wantedChoiceId input@(ChoiceInput currentChoiceId bounds _)
    | wantedChoiceId == currentChoiceId = ChoiceInput choiceId bounds chosenNum

  updateChoice _ input = input

handleAction settings ResetSimulator = do
  oldContract <- use _oldContract
  currContract <- editorGetValue
  let
    newContract = fromMaybe mempty $ oldContract <|> currContract
  editorSetValue newContract
  resetContract
  setOraclePrice settings

handleAction settings ResetContract = do
  resetContract
  setOraclePrice settings

handleAction settings Undo = do
  modifying _marloweState tailIfNotEmpty
  mCurrContract <- use _currentContract
  case mCurrContract of
    Just currContract -> do
      editorSetValue (show $ genericPretty currContract)
      setOraclePrice settings
    Nothing -> pure unit

handleAction _ (SelectHole hole) = assign _selectedHole hole

handleAction _ (ChangeSimulationView view) = do
  assign _bottomPanelView view
  assign _showBottomPanel true
  editorResize

handleAction _ (ChangeHelpContext help) = do
  assign _helpContext help
  scrollHelpPanel

handleAction _ (ShowRightPanel val) = assign _showRightPanel val

handleAction _ (ShowBottomPanel val) = do
  assign _showBottomPanel val
  editorResize

handleAction _ (ShowErrorDetail val) = assign _showErrorDetail val

handleAction _ SetBlocklyCode = pure unit

handleAction _ EditHaskell = pure unit

handleAction _ EditJavascript = pure unit

handleAction _ EditActus = pure unit

handleAction settings AnalyseContract = do
  currContract <- use _currentContract
  currState <- getAsMuchStateAsPossible
  case currContract of
    Nothing -> pure unit
    Just contract -> do
      assign _analysisState (WarningAnalysis Loading)
      response <- checkContractForWarnings contract currState
      assign _analysisState (WarningAnalysis response)
  where
  checkContractForWarnings contract state = runAjax $ (flip runReaderT) settings (Server.postMarloweanalysis (MSReq.Request { onlyAssertions: false, contract, state }))

handleAction settings AnalyseReachabilityContract = do
  currContract <- use _currentContract
  currState <- getAsMuchStateAsPossible
  case currContract of
    Nothing -> pure unit
    Just contract -> do
      newReachabilityAnalysisState <- startReachabilityAnalysis settings contract currState
      assign _analysisState (ReachabilityAnalysis newReachabilityAnalysisState)

handleAction _ Save = pure unit

handleAction _ (InitMarloweProject contents) = do
  editorSetValue contents
  liftEffect $ LocalStorage.setItem marloweBufferLocalStorageKey contents
  assign _hasUnsavedChanges' false

handleAction _ MarkProjectAsSaved = assign _hasUnsavedChanges' false

setOraclePrice ::
  forall m.
  MonadAff m =>
  SPSettings_ SPParams_ -> HalogenM State Action ChildSlots Void m Unit
setOraclePrice settings = do
  execState <- use (_currentMarloweState <<< _executionState)
  case execState of
    SimulationRunning esr -> do
      let
        (Parties actions) = esr.possibleActions
      case Map.lookup (Role "kraken") actions of
        Just acts -> do
          case Array.head (Map.toUnfoldable acts) of
            Just (Tuple (ChoiceInputId choiceId@(ChoiceId pair _)) _) -> do
              price <- getPrice settings "kraken" pair
              handleAction settings (SetChoice choiceId price)
            _ -> pure unit
        Nothing -> pure unit
    _ -> pure unit

type Resp
  = { result :: { price :: Number }, allowance :: { remaining :: Number, upgrade :: String, cost :: Number } }

getPrice :: forall m. MonadAff m => SPSettings_ SPParams_ -> String -> String -> HalogenM State Action ChildSlots Void m BigInteger
getPrice settings exchange pair = do
  result <- runAjax (runReaderT (Server.getApiOracleByExchangeByPair exchange pair) settings)
  calculatedPrice <-
    liftEffect case result of
      NotAsked -> pure "0"
      Loading -> pure "0"
      Failure e -> do
        log $ "Failure" <> errorToString e
        pure "0"
      Success (RawJson json) -> do
        let
          response :: Either (NonEmptyList ForeignError) Resp
          response =
            runExcept
              $ do
                  foreignJson <- parseJSON json
                  decode foreignJson
        case response of
          Right resp -> do
            let
              price = fromNumber resp.result.price
            let
              adjustedPrice = price * fromNumber 100000000.0
            log $ "Got price: " <> show resp.result.price <> ", remaining calls: " <> show resp.allowance.remaining
            pure $ Decimal.toString (truncated adjustedPrice)
          Left err -> do
            log $ "Left " <> show err
            pure "0"
  let
    price = fromMaybe zero (fromString calculatedPrice)
  pure price

getCurrentContract :: forall m. HalogenM State Action ChildSlots Void m String
getCurrentContract = do
  oldContract <- use _oldContract
  currContract <- editorGetValue
  pure $ fromMaybe mempty $ oldContract <|> currContract

runAjax ::
  forall m a.
  ExceptT AjaxError (HalogenM State Action ChildSlots Void m) a ->
  HalogenM State Action ChildSlots Void m (WebData a)
runAjax action = RemoteData.fromEither <$> runExceptT action

scrollHelpPanel :: forall m. MonadEffect m => HalogenM State Action ChildSlots Void m Unit
scrollHelpPanel =
  liftEffect do
    window <- Web.window
    document <- toDocument <$> W.document window
    mSidePanel <- WC.item 0 =<< D.getElementsByClassName "sidebar-composer" document
    mDocPanel <- WC.item 0 =<< D.getElementsByClassName "documentation-panel" document
    case mSidePanel, mDocPanel of
      Just sidePanel, Just docPanel -> do
        sidePanelHeight <- E.scrollHeight sidePanel
        docPanelHeight <- E.scrollHeight docPanel
        availableHeight <- E.clientHeight sidePanel
        let
          newScrollHeight =
            if sidePanelHeight < availableHeight then
              sidePanelHeight
            else
              sidePanelHeight - docPanelHeight - 120.0
        setScrollTop newScrollHeight sidePanel
      _, _ -> pure unit

editorSetTheme :: forall state action msg m. HalogenM state action ChildSlots msg m Unit
editorSetTheme = void $ query _marloweEditorSlot unit (Monaco.SetTheme MM.daylightTheme.name unit)

editorResize :: forall state action msg m. HalogenM state action ChildSlots msg m Unit
editorResize = void $ query _marloweEditorSlot unit (Monaco.Resize unit)

editorSetValue :: forall state action msg m. String -> HalogenM state action ChildSlots msg m Unit
editorSetValue contents = void $ query _marloweEditorSlot unit (Monaco.SetText contents unit)

editorGetValue :: forall state action msg m. HalogenM state action ChildSlots msg m (Maybe String)
editorGetValue = query _marloweEditorSlot unit (Monaco.GetText identity)

saveInitialState :: forall m. MonadEffect m => HalogenM State Action ChildSlots Void m Unit
saveInitialState = do
  oldContract <- editorGetValue
  modifying _oldContract
    ( \x -> case x of
        Nothing -> Just $ fromMaybe "" oldContract
        _ -> x
    )

resetContract :: forall m. HalogenM State Action ChildSlots Void m Unit
resetContract = do
  newContract <- editorGetValue
  assign _marloweState $ NEL.singleton emptyMarloweState
  assign _oldContract Nothing
  updateContractInState $ fromMaybe "" newContract

-- FIXME: remove this
editorSetMarkers :: forall m. MonadEffect m => Array IMarker -> HalogenM State Action ChildSlots Void m Unit
editorSetMarkers markers = do
  let
    warnings = filter (\{ severity } -> isWarning severity) markers

    trimHoles =
      map
        ( \marker ->
            let
              trimmedMessage =
                if String.take 6 marker.source == "Hole: " then
                  String.takeWhile (\c -> c /= codePointFromChar '\n') marker.message
                else
                  marker.message
            in
              marker { message = trimmedMessage }
        )
        warnings
  let
    errors = filter (\{ severity } -> isError severity) markers
  assign (_marloweState <<< _Head <<< _editorWarnings) trimHoles
  assign (_marloweState <<< _Head <<< _editorErrors) errors
  pure unit
