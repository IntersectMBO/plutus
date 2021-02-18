module SimulationPage.State
  ( handleAction
  , editorResize
  , editorSetTheme
  , editorGetValue
  , getCurrentContract
  ) where

import Prelude hiding (div)
import BottomPanel.State (handleAction) as BottomPanel
import BottomPanel.Types (Action(..), State) as BottomPanel
import Control.Monad.Except (ExceptT, lift, runExcept, runExceptT)
import Control.Monad.Maybe.Extra (hoistMaybe)
import Control.Monad.Maybe.Trans (MaybeT(..), runMaybeT)
import Control.Monad.Reader (class MonadAsk, asks, runReaderT)
import Data.Array (snoc)
import Data.Array as Array
import Data.BigInteger (BigInteger, fromString)
import Data.Decimal (truncated, fromNumber)
import Data.Decimal as Decimal
import Data.Either (Either(..), hush)
import Data.Lens (_Just, assign, modifying, over, set, to, use)
import Data.Lens.Extra (peruse)
import Data.Lens.NonEmptyList (_Head)
import Data.List.NonEmpty (last, singleton)
import Data.List.Types (NonEmptyList)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe, maybe)
import Data.NonEmptyList.Extra (extendWith, tailIfNotEmpty)
import Data.RawJson (RawJson(..))
import Data.Tuple (Tuple(..))
import Effect.Aff.Class (class MonadAff)
import Effect.Class (class MonadEffect, liftEffect)
import Effect.Console (log)
import Env (Env)
import Foreign.Generic (ForeignError, decode)
import Foreign.JSON (parseJSON)
import Halogen (HalogenM, get, query)
import Halogen.Extra (mapSubmodule)
import Halogen.Monaco (Query(..)) as Monaco
import LocalStorage as LocalStorage
import MainFrame.Types (ChildSlots, _simulatorEditorSlot)
import Marlowe as Server
import Marlowe.Extended (fillTemplate, toCore, typeToLens)
import Marlowe.Extended as EM
import Marlowe.Holes (fromTerm)
import Marlowe.Monaco as MM
import Marlowe.Parser (parseContract)
import Marlowe.Semantics (ChoiceId(..), Input(..), Party(..), inBounds)
import Marlowe.Semantics as S
import Network.RemoteData (RemoteData(..))
import Network.RemoteData as RemoteData
import Servant.PureScript.Ajax (AjaxError, errorToString)
import SimulationPage.Types (Action(..), ActionInput(..), ActionInputId(..), BottomPanelView, ExecutionState(..), Parties(..), State, _SimulationNotStarted, _SimulationRunning, _bottomPanelState, _currentMarloweState, _executionState, _extendedContract, _helpContext, _initialSlot, _marloweState, _moveToAction, _possibleActions, _showRightPanel, _templateContent, emptyExecutionStateWithSlot, emptyMarloweState, mapPartiesActionInput)
import Simulator (applyInput, inFuture, moveToSignificantSlot, moveToSlot, nextSignificantSlot, updateMarloweState, updatePossibleActions, updateStateP)
import StaticData (simulatorBufferLocalStorageKey)
import Text.Pretty (genericPretty)
import Types (WebData)
import Web.DOM.Document as D
import Web.DOM.Element (setScrollTop)
import Web.DOM.Element as E
import Web.DOM.HTMLCollection as WC
import Web.HTML as Web
import Web.HTML.HTMLDocument (toDocument)
import Web.HTML.Window as W

toBottomPanel ::
  forall m a.
  Functor m =>
  HalogenM (BottomPanel.State BottomPanelView) (BottomPanel.Action BottomPanelView Action) ChildSlots Void m a ->
  HalogenM State Action ChildSlots Void m a
toBottomPanel = mapSubmodule _bottomPanelState BottomPanelAction

handleAction ::
  forall m.
  MonadAff m =>
  MonadAsk Env m =>
  Action ->
  HalogenM State Action ChildSlots Void m Unit
handleAction Init = do
  editorSetTheme
  mContents <- liftEffect $ LocalStorage.getItem simulatorBufferLocalStorageKey
  handleAction $ LoadContract $ fromMaybe "" mContents

handleAction (SetInitialSlot initialSlot) = do
  assign (_currentMarloweState <<< _executionState <<< _SimulationNotStarted <<< _initialSlot) initialSlot
  setOraclePrice

handleAction (SetIntegerTemplateParam templateType key value) = do
  modifying (_currentMarloweState <<< _executionState <<< _SimulationNotStarted <<< _templateContent <<< typeToLens templateType) (Map.insert key value)
  setOraclePrice

handleAction StartSimulation =
  void
    $ runMaybeT do
        initialSlot <- MaybeT $ peruse (_currentMarloweState <<< _executionState <<< _SimulationNotStarted <<< _initialSlot)
        extendedContract <- MaybeT $ peruse (_currentMarloweState <<< _executionState <<< _SimulationNotStarted <<< _extendedContract <<< _Just)
        templateContent <- MaybeT $ peruse (_currentMarloweState <<< _executionState <<< _SimulationNotStarted <<< _templateContent)
        contract <- hoistMaybe $ toCore $ fillTemplate templateContent (extendedContract :: EM.Contract)
        modifying _marloweState (extendWith (updatePossibleActions <<< updateStateP <<< (set _executionState (emptyExecutionStateWithSlot initialSlot (contract :: S.Contract)))))
        lift $ updateContractInEditor

handleAction (MoveSlot slot) = do
  inTheFuture <- inFuture <$> get <*> pure slot
  significantSlot <- use (_marloweState <<< _Head <<< to nextSignificantSlot)
  when inTheFuture do
    if slot >= (fromMaybe zero significantSlot) then
      moveToSignificantSlot slot
    else
      moveToSlot slot
    updateContractInEditor

handleAction (SetSlot slot) = do
  assign (_currentMarloweState <<< _executionState <<< _SimulationRunning <<< _possibleActions <<< _moveToAction) (Just $ MoveToSlot slot)
  setOraclePrice

handleAction (AddInput input bounds) = do
  when validInput do
    applyInput ((flip snoc) input)
    updateContractInEditor
  where
  validInput = case input of
    (IChoice _ chosenNum) -> inBounds chosenNum bounds
    _ -> true

handleAction (SetChoice choiceId chosenNum) = updateMarloweState (over (_executionState <<< _SimulationRunning <<< _possibleActions) (mapPartiesActionInput (updateChoice choiceId)))
  where
  updateChoice :: ChoiceId -> ActionInput -> ActionInput
  updateChoice wantedChoiceId input@(ChoiceInput currentChoiceId bounds _)
    | wantedChoiceId == currentChoiceId = ChoiceInput choiceId bounds chosenNum

  updateChoice _ input = input

handleAction ResetSimulator = do
  modifying _marloweState (singleton <<< last)
  updateContractInEditor

handleAction Undo = do
  modifying _marloweState tailIfNotEmpty
  updateContractInEditor

handleAction (LoadContract contents) = do
  liftEffect $ LocalStorage.setItem simulatorBufferLocalStorageKey contents
  let
    mExtendedContract = do
      termContract <- hush $ parseContract contents
      fromTerm termContract :: Maybe EM.Contract
  assign _marloweState $ singleton $ emptyMarloweState mExtendedContract
  updateContractInEditor

handleAction (BottomPanelAction (BottomPanel.PanelAction action)) = handleAction action

handleAction (BottomPanelAction action) = do
  toBottomPanel (BottomPanel.handleAction action)
  editorResize

handleAction (ChangeHelpContext help) = do
  assign _helpContext help
  scrollHelpPanel

handleAction (ShowRightPanel val) = assign _showRightPanel val

handleAction EditSource = pure unit

setOraclePrice ::
  forall m.
  MonadAff m =>
  MonadAsk Env m =>
  HalogenM State Action ChildSlots Void m Unit
setOraclePrice = do
  execState <- use (_currentMarloweState <<< _executionState)
  case execState of
    SimulationRunning esr -> do
      let
        (Parties actions) = esr.possibleActions
      case Map.lookup (Role "kraken") actions of
        Just acts -> do
          case Array.head (Map.toUnfoldable acts) of
            Just (Tuple (ChoiceInputId choiceId@(ChoiceId pair _)) _) -> do
              price <- getPrice "kraken" pair
              handleAction (SetChoice choiceId price)
            _ -> pure unit
        Nothing -> pure unit
    _ -> pure unit

type Resp
  = { result :: { price :: Number }, allowance :: { remaining :: Number, upgrade :: String, cost :: Number } }

getPrice ::
  forall m.
  MonadAff m =>
  MonadAsk Env m =>
  String ->
  String ->
  HalogenM State Action ChildSlots Void m BigInteger
getPrice exchange pair = do
  settings <- asks _.ajaxSettings
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

getCurrentContract :: forall m. HalogenM State Action ChildSlots Void m (Maybe String)
getCurrentContract = editorGetValue

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
editorSetTheme = void $ query _simulatorEditorSlot unit (Monaco.SetTheme MM.daylightTheme.name unit)

editorResize :: forall state action msg m. HalogenM state action ChildSlots msg m Unit
editorResize = void $ query _simulatorEditorSlot unit (Monaco.Resize unit)

editorSetValue :: forall state action msg m. String -> HalogenM state action ChildSlots msg m Unit
editorSetValue contents = void $ query _simulatorEditorSlot unit (Monaco.SetText contents unit)

editorGetValue :: forall state action msg m. HalogenM state action ChildSlots msg m (Maybe String)
editorGetValue = query _simulatorEditorSlot unit (Monaco.GetText identity)

updateContractInEditor ::
  forall m.
  MonadAff m =>
  MonadAsk Env m =>
  HalogenM State Action ChildSlots Void m Unit
updateContractInEditor = do
  executionState <- use (_currentMarloweState <<< _executionState)
  editorSetValue
    ( case executionState of
        SimulationRunning runningState -> show $ genericPretty runningState.contract
        SimulationNotStarted notStartedState -> maybe "No contract" (show <<< genericPretty) notStartedState.extendedContract -- This "No contract" should never happen if we get valid contracts from editors 
    )
  setOraclePrice
