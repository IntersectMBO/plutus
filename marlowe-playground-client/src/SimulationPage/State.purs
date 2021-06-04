module SimulationPage.State
  ( handleAction
  , editorSetTheme
  , editorGetValue
  , getCurrentContract
  , mkState
  ) where

import Prelude hiding (div)
import BottomPanel.State (handleAction) as BottomPanel
import BottomPanel.Types (Action(..), State, initialState) as BottomPanel
import Control.Monad.Except (ExceptT, lift, runExcept, runExceptT)
import Control.Monad.Maybe.Trans (MaybeT(..), runMaybeT)
import Control.Monad.Reader (class MonadAsk, asks, runReaderT)
import Data.Array (snoc)
import Data.Array as Array
import Data.BigInteger (BigInteger, fromString)
import Data.Decimal (truncated, fromNumber)
import Data.Decimal as Decimal
import Data.Either (Either(..), hush)
import Data.Foldable (for_)
import Data.Lens (_Just, assign, modifying, over, set, use)
import Data.Lens.Extra (peruse)
import Data.List.NonEmpty (last)
import Data.List.NonEmpty as NEL
import Data.List.Types (NonEmptyList)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe)
import Data.NonEmptyList.Extra (extendWith, tailIfNotEmpty)
import Data.RawJson (RawJson(..))
import Data.String (splitAt)
import Data.Tuple (Tuple(..))
import Data.Tuple.Nested (type (/\), (/\))
import Effect.Aff.Class (class MonadAff)
import Effect.Class (class MonadEffect, liftEffect)
import Effect.Console (log)
import Env (Env)
import Foreign.Generic (ForeignError, decode)
import Foreign.JSON (parseJSON)
import Halogen (HalogenM, get, query, tell)
import Halogen.Extra (mapSubmodule)
import Halogen.Monaco (Query(..)) as Monaco
import Help (HelpContext(..))
import MainFrame.Types (ChildSlots, _simulatorEditorSlot)
import Marlowe as Server
import Marlowe.Holes (Location(..), getLocation)
import Marlowe.Monaco as MM
import Marlowe.Parser (parseContract)
import Marlowe.Semantics (ChoiceId(..), Input(..), Party(..), inBounds)
import Marlowe.Template (fillTemplate, typeToLens)
import Network.RemoteData (RemoteData(..))
import Network.RemoteData as RemoteData
import Servant.PureScript.Ajax (AjaxError, errorToString)
import SessionStorage as SessionStorage
import SimulationPage.Lenses (_bottomPanelState, _decorationIds, _helpContext, _showRightPanel)
import SimulationPage.Types (Action(..), BottomPanelView(..), State)
import Simulator.Lenses (_SimulationNotStarted, _SimulationRunning, _currentContract, _currentMarloweState, _executionState, _initialSlot, _marloweState, _moveToAction, _possibleActions, _templateContent, _termContract)
import Simulator.State (applyInput, emptyExecutionStateWithSlot, emptyMarloweState, inFuture, mapPartiesActionInput, moveToSlot, updateMarloweState, updatePossibleActions, applyPendingInputs)
import Simulator.Types (ActionInput(..), ActionInputId(..), ExecutionState(..), Parties(..))
import StaticData (simulatorBufferLocalStorageKey)
import Types (WebData)
import Web.DOM.Document as D
import Web.DOM.Element (setScrollTop)
import Web.DOM.Element as E
import Web.DOM.HTMLCollection as WC
import Web.HTML as Web
import Web.HTML.HTMLDocument (toDocument)
import Web.HTML.Window as W

mkState :: State
mkState =
  { showRightPanel: true
  , marloweState: NEL.singleton (emptyMarloweState Nothing)
  , helpContext: MarloweHelp
  , bottomPanelState: BottomPanel.initialState CurrentStateView
  , decorationIds: []
  }

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
  contents <- fromMaybe "" <$> (liftEffect $ SessionStorage.getItem simulatorBufferLocalStorageKey)
  handleAction $ LoadContract contents

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
        termContract <- MaybeT $ peruse (_currentMarloweState <<< _executionState <<< _SimulationNotStarted <<< _termContract <<< _Just)
        templateContent <- MaybeT $ peruse (_currentMarloweState <<< _executionState <<< _SimulationNotStarted <<< _templateContent)
        let
          contract = fillTemplate templateContent termContract
        -- The marloweState is a non empty list of an object that includes the ExecutionState (SimulationRunning | SimulationNotStarted)
        -- Inside the SimulationNotStarted we can find the information needed to start the simulation. By running
        -- this code inside of a maybeT, we make sure that the Head of the list has the state SimulationNotStarted
        modifying
          _marloweState
          ( extendWith
              ( updatePossibleActions
                  <<< applyPendingInputs
                  <<< (set _executionState (emptyExecutionStateWithSlot initialSlot contract))
              )
          )
        lift $ updateOracleAndContractEditor

handleAction (MoveSlot slot) = do
  inTheFuture <- inFuture <$> get <*> pure slot
  when inTheFuture do
    moveToSlot slot
    updateOracleAndContractEditor

handleAction (SetSlot slot) = do
  assign (_currentMarloweState <<< _executionState <<< _SimulationRunning <<< _possibleActions <<< _moveToAction) (Just $ MoveToSlot slot)
  setOraclePrice

handleAction (AddInput input bounds) = do
  when validInput do
    applyInput ((flip snoc) input)
    updateOracleAndContractEditor
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
  modifying _marloweState (NEL.singleton <<< last)
  updateOracleAndContractEditor

handleAction Undo = do
  modifying _marloweState tailIfNotEmpty
  updateOracleAndContractEditor

handleAction (LoadContract contents) = do
  liftEffect $ SessionStorage.setItem simulatorBufferLocalStorageKey contents
  let
    mTermContract = hush $ parseContract contents
  assign _marloweState $ NEL.singleton $ emptyMarloweState mTermContract
  editorSetValue contents

handleAction (BottomPanelAction (BottomPanel.PanelAction action)) = handleAction action

handleAction (BottomPanelAction action) = do
  toBottomPanel (BottomPanel.handleAction action)

handleAction (ChangeHelpContext help) = do
  assign _helpContext help
  scrollHelpPanel

handleAction (ShowRightPanel val) = assign _showRightPanel val

handleAction EditSource = pure unit

stripPair :: String -> Boolean /\ String
stripPair pair = case splitAt 4 pair of
  { before, after }
    | before == "inv-" -> true /\ after
    | before == "dir-" -> false /\ after
  _ -> false /\ pair

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
              let
                inverse /\ strippedPair = stripPair pair
              price <- getPrice inverse "kraken" strippedPair
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
  Boolean ->
  String ->
  String ->
  HalogenM State Action ChildSlots Void m BigInteger
getPrice inverse exchange pair = do
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

              adjustedPrice = (if inverse then one / price else price) * fromNumber 100000000.0
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

editorSetValue :: forall state action msg m. String -> HalogenM state action ChildSlots msg m Unit
editorSetValue contents = void $ query _simulatorEditorSlot unit (Monaco.SetText contents unit)

editorGetValue :: forall state action msg m. HalogenM state action ChildSlots msg m (Maybe String)
editorGetValue = query _simulatorEditorSlot unit (Monaco.GetText identity)

updateOracleAndContractEditor ::
  forall m.
  MonadAff m =>
  MonadAsk Env m =>
  HalogenM State Action ChildSlots Void m Unit
updateOracleAndContractEditor = do
  mContract <- peruse _currentContract
  -- Update the decorations around the current part of the running contract
  case getLocation <$> mContract of
    Just (Range r) -> do
      let
        decorationOptions = { isWholeLine: false, className: "monaco-simulation-text-decoration", linesDecorationsClassName: "monaco-simulation-line-decoration" }
      oldDecorationIds <- use _decorationIds
      mNewDecorationIds <- query _simulatorEditorSlot unit $ Monaco.SetDeltaDecorations oldDecorationIds [ { range: r, options: decorationOptions } ] identity
      for_ mNewDecorationIds (assign _decorationIds)
      void $ query _simulatorEditorSlot unit $ tell $ Monaco.RevealRange r
    _ -> pure unit
  setOraclePrice
