module Simulation.State where

import Control.Alternative (map, void, when, (<*>), (<|>))
import Control.Monad.Except (ExceptT, runExceptT, runExcept)
import Control.Monad.Reader (runReaderT)
import Data.EuclideanRing ((*))
import Data.RawJson (RawJson(..))
import Data.Array (delete, filter, intercalate, snoc, sortWith)
import Data.Array as Array
import Data.BigInteger (BigInteger, fromString, fromInt)
import Data.Decimal (truncated, fromNumber)
import Data.Decimal as Decimal
import Data.Either (Either(..))
import Data.Enum (toEnum, upFromIncluding)
import Data.HeytingAlgebra (not, (&&))
import Data.Lens (assign, has, modifying, only, over, preview, to, use, view, (^.))
import Data.Lens.Extra (peruse)
import Data.Lens.Index (ix)
import Data.Lens.Iso.Newtype (_Newtype)
import Data.Lens.NonEmptyList (_Head)
import Data.List.NonEmpty as NEL
import Data.List.Types (NonEmptyList)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Newtype (wrap)
import Data.NonEmptyList.Extra (tailIfNotEmpty)
import Data.String (codePointFromChar)
import Data.String as String
import Data.Traversable (for_, traverse)
import Data.Tuple (Tuple(..), snd)
import Effect.Aff.Class (class MonadAff, liftAff)
import Effect.Class (class MonadEffect, liftEffect)
import Effect.Console (log)
import FileEvents (readFileFromDragEvent)
import FileEvents as FileEvents
import Foreign.Generic (ForeignError, decode)
import Foreign.JSON (parseJSON)
import Halogen (HalogenM, get, query)
import Halogen.Classes (aHorizontal, activeClasses, bold, closeDrawerIcon, codeEditor, expanded, fullHeight, infoIcon, noMargins, panelSubHeaderSide, plusBtn, pointer, scroll, sidebarComposer, smallBtn, spanText, textSecondaryColor, uppercase)
import Halogen.Classes as Classes
import Halogen.HTML (ClassName(..), ComponentHTML, HTML, a, article, aside, b_, br_, button, div, em_, h6, h6_, img, input, li, option, p, p_, section, select, slot, small, strong_, text, ul, ul_)
import Halogen.HTML.Events (onClick, onSelectedIndexChange, onValueChange)
import Halogen.HTML.Properties (InputType(..), alt, class_, classes, enabled, placeholder, src, type_, value)
import Halogen.HTML.Properties as HTML
import Halogen.Monaco (Message(..), Query(..)) as Monaco
import Halogen.Monaco (monacoComponent)
import Help (HelpContext(..), toHTML)
import LocalStorage as LocalStorage
import MainFrame.Types (ChildSlots, _marloweEditorSlot)
import Marlowe (SPParams_)
import Marlowe as Server
import Marlowe.Linter as Linter
import Marlowe.Monaco (updateAdditionalContext)
import Marlowe.Monaco as MM
import Marlowe.Parser (parseContract)
import Marlowe.Semantics (AccountId, Bound(..), ChoiceId(..), Input(..), Party(..), PubKey, Token, emptyState, inBounds, showPrettyToken)
import Marlowe.Symbolic.Types.Request as MSReq
import Monaco (IMarker, isError, isWarning)
import Monaco (getModel, getMonaco, setTheme, setValue) as Monaco
import Network.RemoteData (RemoteData(..))
import Network.RemoteData as RemoteData
import Prelude (class Show, Unit, Void, bind, bottom, const, discard, eq, flip, identity, mempty, pure, show, unit, zero, ($), (-), (/=), (<), (<$>), (<<<), (<>), (=<<), (==), (>=))
import Projects.Types (Lang(..))
import Reachability (startReachabilityAnalysis)
import Servant.PureScript.Ajax (AjaxError, errorToString)
import Servant.PureScript.Settings (SPSettings_)
import Simulation.BottomPanel (bottomPanel)
import Simulation (ActionInput(..), ActionInputId(..), ExecutionState(..), Parties(..), _SimulationNotStarted, _SimulationRunning, _editorErrors, _editorWarnings, _executionState, _initialSlot, _moveToAction, _pendingInputs, _possibleActions, _slot, applyInput, emptyExecutionStateWithSlot, emptyMarloweState, getAsMuchStateAP, hasHistory, inFuture, mapPartiesActionInput, moveToSignificantSlot, moveToSlot, nextSignificantSlot, otherActionsParty, updateContractInState, updateMarloweState)
import Simulation.Types (Action(..), AnalysisState(..), State, WebData, _activeDemo, _analysisState, _bottomPanelView, _currentContract, _currentMarloweState, _editorKeybindings, _helpContext, _marloweState, _oldContract, _selectedHole, _showBottomPanel, _showErrorDetail, _showRightPanel, _source, isContractValid)
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
  assign _selectedHole Nothing
  liftEffect $ LocalStorage.setItem marloweBufferLocalStorageKey text
  updateContractInState text
  assign _activeDemo ""
  executionState <- use (_currentMarloweState <<< _executionState)
  let
    state = case executionState of
      SimulationRunning runRecord -> runRecord.state
      SimulationNotStarted notRunRecord -> emptyState $ notRunRecord.initialSlot

    (Tuple markerData additionalContext) = Linter.markers state text
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
    assign _activeDemo key
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
  currState <- getAsMuchStateAP
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
  currState <- getAsMuchStateAP
  case currContract of
    Nothing -> pure unit
    Just contract -> do
      newReachabilityAnalysisState <- startReachabilityAnalysis settings contract currState
      assign _analysisState (ReachabilityAnalysis newReachabilityAnalysisState)

handleAction _ Save = pure unit

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
