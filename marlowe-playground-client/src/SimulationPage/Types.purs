-- A separate module for types that are shared between Simulation and Simulation.BottomPanel
module SimulationPage.Types where

import Prelude
import Analytics (class IsEvent, Event)
import Analytics as A
import BottomPanel.Types as BottomPanel
import Data.Array (mapMaybe)
import Data.BigInteger (BigInteger)
import Data.Either (Either(..))
import Data.Generic.Rep (class Generic)
import Data.Generic.Rep.Show (genericShow)
import Data.Lens (Getter', Lens', Prism', Traversal', Optic', lens, preview, prism, set, to)
import Data.Lens.At (at)
import Data.Lens.Index (ix)
import Data.Lens.Iso.Newtype (_Newtype)
import Data.Lens.NonEmptyList (_Head)
import Data.Lens.Record (prop)
import Data.List.NonEmpty as NEL
import Data.List.Types (NonEmptyList)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), maybe)
import Data.Newtype (class Newtype)
import Data.Profunctor.Choice (class Choice)
import Data.Profunctor.Strong (class Strong)
import Data.Symbol (SProxy(..))
import Foreign.Generic (class Decode, class Encode, genericDecode, genericEncode)
import Help (HelpContext(..))
import Marlowe.Extended (IntegerTemplateType, TemplateContent, getPlaceholderIds, initializeTemplateContent)
import Marlowe.Extended as EM
import Marlowe.Holes (Holes)
import Marlowe.Semantics (AccountId, Assets, Bound, ChoiceId, ChosenNum, Contract, Input, Party(..), Payment, Slot, SlotInterval, Token, TransactionError, TransactionInput, TransactionWarning, aesonCompatibleOptions, emptyState)
import Marlowe.Semantics as S
import Marlowe.Symbolic.Types.Response (Result)
import Monaco (IMarker)
import Network.RemoteData (RemoteData)

data ActionInputId
  = DepositInputId AccountId Party Token BigInteger
  | ChoiceInputId ChoiceId
  | NotifyInputId
  | MoveToSlotId

derive instance eqActionInputId :: Eq ActionInputId

derive instance ordActionInputId :: Ord ActionInputId

derive instance genericActionInputId :: Generic ActionInputId _

instance encodeActionInputId :: Encode ActionInputId where
  encode a = genericEncode aesonCompatibleOptions a

instance decodeActionInputId :: Decode ActionInputId where
  decode = genericDecode aesonCompatibleOptions

-- | On the front end we need Actions however we also need to keep track of the current
-- | choice that has been set for Choices
data ActionInput
  = DepositInput AccountId Party Token BigInteger
  | ChoiceInput ChoiceId (Array Bound) ChosenNum
  | NotifyInput
  | MoveToSlot Slot

derive instance eqActionInput :: Eq ActionInput

derive instance ordActionInput :: Ord ActionInput

derive instance genericActionInput :: Generic ActionInput _

instance encodeActionInput :: Encode ActionInput where
  encode a = genericEncode aesonCompatibleOptions a

instance decodeActionInput :: Decode ActionInput where
  decode = genericDecode aesonCompatibleOptions

newtype Parties
  = Parties (Map Party (Map ActionInputId ActionInput))

derive instance newtypeParties :: Newtype Parties _

derive newtype instance semigroupParties :: Semigroup Parties

derive newtype instance monoidParties :: Monoid Parties

mapPartiesActionInput :: (ActionInput -> ActionInput) -> Parties -> Parties
mapPartiesActionInput f (Parties m) = Parties $ (map <<< map) f m

derive newtype instance encodeParties :: Encode Parties

derive newtype instance decodeParties :: Decode Parties

_actionInput :: Party -> ActionInputId -> Traversal' Parties ActionInput
_actionInput party id = _Newtype <<< ix party <<< ix id

_otherActions :: Traversal' Parties (Map ActionInputId ActionInput)
_otherActions = _Newtype <<< ix otherActionsParty

_moveToAction :: Lens' Parties (Maybe ActionInput)
_moveToAction = lens get' set'
  where
  get' = preview (_actionInput otherActionsParty MoveToSlotId)

  set' p ma =
    let
      m = case preview _otherActions p, ma of
        Nothing, Nothing -> Nothing
        Just m', Nothing -> Just $ Map.delete MoveToSlotId m'
        Nothing, Just a -> Just $ Map.singleton MoveToSlotId a
        Just m', Just a -> Just $ Map.insert MoveToSlotId a m'
    in
      set (_Newtype <<< at otherActionsParty) m p

data MarloweEvent
  = InputEvent TransactionInput
  | OutputEvent SlotInterval Payment

derive instance genericMarloweEvent :: Generic MarloweEvent _

instance encodeMarloweEvent :: Encode MarloweEvent where
  encode a = genericEncode aesonCompatibleOptions a

instance decodeMarloweEvent :: Decode MarloweEvent where
  decode = genericDecode aesonCompatibleOptions

-- We have a special person for notifications
otherActionsParty :: Party
otherActionsParty = Role "marlowe_other_actions"

type ExecutionStateRecord
  = { possibleActions :: Parties
    , pendingInputs :: Array Input
    , transactionError :: Maybe TransactionError
    , transactionWarnings :: Array TransactionWarning
    , log :: Array MarloweEvent
    , state :: S.State
    , slot :: Slot
    , moneyInContract :: Assets
    , contract :: S.Contract
    }

_possibleActions :: forall s a. Lens' { possibleActions :: a | s } a
_possibleActions = prop (SProxy :: SProxy "possibleActions")

_pendingInputs :: forall s a. Lens' { pendingInputs :: a | s } a
_pendingInputs = prop (SProxy :: SProxy "pendingInputs")

_state :: forall s a. Lens' { state :: a | s } a
_state = prop (SProxy :: SProxy "state")

_transactionError :: forall s a. Lens' { transactionError :: a | s } a
_transactionError = prop (SProxy :: SProxy "transactionError")

_transactionWarnings :: forall s a. Lens' { transactionWarnings :: a | s } a
_transactionWarnings = prop (SProxy :: SProxy "transactionWarnings")

_slot :: forall s a. Lens' { slot :: a | s } a
_slot = prop (SProxy :: SProxy "slot")

_moneyInContract :: forall s a. Lens' { moneyInContract :: a | s } a
_moneyInContract = prop (SProxy :: SProxy "moneyInContract")

_contract :: forall s a. Lens' { contract :: a | s } a
_contract = prop (SProxy :: SProxy "contract")

_log :: forall s a. Lens' { log :: a | s } a
_log = prop (SProxy :: SProxy "log")

_payments :: forall s. Getter' { log :: Array MarloweEvent | s } (Array Payment)
_payments = _log <<< to (mapMaybe f)
  where
  f (InputEvent _) = Nothing

  f (OutputEvent _ payment) = Just payment

type InitialConditionsRecord
  = { initialSlot :: Slot
    , extendedContract :: Maybe EM.Contract
    , templateContent :: TemplateContent
    }

_initialSlot :: forall s a. Lens' { initialSlot :: a | s } a
_initialSlot = prop (SProxy :: SProxy "initialSlot")

_extendedContract :: forall s a. Lens' { extendedContract :: a | s } a
_extendedContract = prop (SProxy :: SProxy "extendedContract")

_templateContent :: forall s a. Lens' { templateContent :: a | s } a
_templateContent = prop (SProxy :: SProxy "templateContent")

data ExecutionState
  = SimulationRunning ExecutionStateRecord
  | SimulationNotStarted InitialConditionsRecord

-- | Prism for the `ExecutionState` constructor of `SimulationRunning`.
_SimulationRunning :: Prism' ExecutionState ExecutionStateRecord
_SimulationRunning =
  prism SimulationRunning
    $ ( \x -> case x of
          SimulationRunning record -> Right record
          anotherCase -> Left anotherCase
      )

-- | Prism for the `ExecutionState` constructor of `SimulationNotStarted`.
_SimulationNotStarted :: Prism' ExecutionState InitialConditionsRecord
_SimulationNotStarted =
  prism SimulationNotStarted
    $ ( \x -> case x of
          SimulationNotStarted record -> Right record
          anotherCase -> Left anotherCase
      )

emptyExecutionStateWithSlot :: Slot -> S.Contract -> ExecutionState
emptyExecutionStateWithSlot sn cont =
  SimulationRunning
    { possibleActions: mempty
    , pendingInputs: mempty
    , transactionError: Nothing
    , transactionWarnings: mempty
    , log: mempty
    , state: emptyState sn
    , slot: sn
    , moneyInContract: mempty
    , contract: cont
    }

simulationNotStartedWithSlot :: Slot -> Maybe EM.Contract -> ExecutionState
simulationNotStartedWithSlot slot mContract =
  SimulationNotStarted
    { initialSlot: slot
    , extendedContract: mContract
    , templateContent: maybe mempty (initializeTemplateContent <<< getPlaceholderIds) mContract
    }

simulationNotStarted :: Maybe EM.Contract -> ExecutionState
simulationNotStarted = simulationNotStartedWithSlot zero

type MarloweState
  = { executionState :: ExecutionState
    , holes :: Holes
    -- NOTE: as part of the marlowe editor and simulator split this part of the
    --       state wont be used, but it is left as it is because it may make sense
    --       to use it as part of task SCP-1642
    , editorErrors :: Array IMarker
    , editorWarnings :: Array IMarker
    }

_executionState :: forall s a. Lens' { executionState :: a | s } a
_executionState = prop (SProxy :: SProxy "executionState")

_editorErrors :: forall s a. Lens' { editorErrors :: a | s } a
_editorErrors = prop (SProxy :: SProxy "editorErrors")

_editorWarnings :: forall s a. Lens' { editorWarnings :: a | s } a
_editorWarnings = prop (SProxy :: SProxy "editorWarnings")

_holes :: forall s a. Lens' { holes :: a | s } a
_holes = prop (SProxy :: SProxy "holes")

--- Language.Haskell.Interpreter ---
_result :: forall s a. Lens' { result :: a | s } a
_result = prop (SProxy :: SProxy "result")

emptyMarloweState :: Maybe EM.Contract -> MarloweState
emptyMarloweState mContract =
  { editorErrors: mempty
  , editorWarnings: mempty
  , holes: mempty
  , executionState: simulationNotStarted mContract
  }

emptyMarloweStateWithSlot :: Slot -> S.Contract -> MarloweState
emptyMarloweStateWithSlot sn cont =
  { editorErrors: mempty
  , editorWarnings: mempty
  , holes: mempty
  , executionState: emptyExecutionStateWithSlot sn cont
  }

--
type State
  = { showRightPanel :: Boolean
    , bottomPanelState :: BottomPanel.State BottomPanelView
    , marloweState :: NonEmptyList MarloweState
    , helpContext :: HelpContext
    }

_showRightPanel :: Lens' State Boolean
_showRightPanel = prop (SProxy :: SProxy "showRightPanel")

_marloweState :: forall s. Lens' { marloweState :: NonEmptyList MarloweState | s } (NonEmptyList MarloweState)
_marloweState = prop (SProxy :: SProxy "marloweState")

_currentMarloweState :: forall s. Lens' { marloweState :: NonEmptyList MarloweState | s } MarloweState
_currentMarloweState = _marloweState <<< _Head

_currentContract :: forall s p. Strong p => Choice p => Optic' p { marloweState :: NonEmptyList MarloweState | s } Contract
_currentContract = _currentMarloweState <<< _executionState <<< _SimulationRunning <<< _contract

_helpContext :: Lens' State HelpContext
_helpContext = prop (SProxy :: SProxy "helpContext")

_bottomPanelState :: Lens' State (BottomPanel.State BottomPanelView)
_bottomPanelState = prop (SProxy :: SProxy "bottomPanelState")

mkState :: State
mkState =
  { showRightPanel: true
  , marloweState: NEL.singleton (emptyMarloweState Nothing)
  , helpContext: MarloweHelp
  , bottomPanelState: BottomPanel.initialState CurrentStateView
  }

data Action
  = Init
  -- marlowe actions
  | SetInitialSlot Slot
  | SetIntegerTemplateParam IntegerTemplateType String BigInteger
  | StartSimulation
  | MoveSlot Slot
  | SetSlot Slot
  | AddInput Input (Array Bound)
  | SetChoice ChoiceId ChosenNum
  | ResetSimulator
  | Undo
  | LoadContract String
  -- simulation view
  -- FIXME: We are not showing a help context. See if we want to bring back this
  --       functionality or delete this code
  | ChangeHelpContext HelpContext
  -- FIXME: This action is not triggerable at the moment. Check if we want to bring
  --        back this functionality or delete this code
  | ShowRightPanel Boolean
  | BottomPanelAction (BottomPanel.Action BottomPanelView Action)
  | EditSource

defaultEvent :: String -> Event
defaultEvent s = A.defaultEvent $ "Simulation." <> s

instance isEventAction :: IsEvent Action where
  toEvent Init = Just $ defaultEvent "Init"
  toEvent (SetInitialSlot _) = Just $ defaultEvent "SetInitialSlot"
  toEvent (SetIntegerTemplateParam templateType key value) = Just $ defaultEvent "SetIntegerTemplateParam"
  toEvent StartSimulation = Just $ defaultEvent "StartSimulation"
  toEvent (MoveSlot _) = Just $ defaultEvent "MoveSlot"
  toEvent (SetSlot _) = Just $ defaultEvent "SetSlot"
  toEvent (AddInput _ _) = Just $ defaultEvent "AddInput"
  toEvent (SetChoice _ _) = Just $ defaultEvent "SetChoice"
  toEvent ResetSimulator = Just $ defaultEvent "ResetSimulator"
  toEvent Undo = Just $ defaultEvent "Undo"
  toEvent (LoadContract _) = Just $ defaultEvent "LoadContract"
  toEvent (ChangeHelpContext help) = Just $ (defaultEvent "ChangeHelpContext") { label = Just $ show help }
  toEvent (ShowRightPanel _) = Just $ defaultEvent "ShowRightPanel"
  toEvent (BottomPanelAction action) = A.toEvent action
  toEvent EditSource = Just $ defaultEvent "EditSource"

data Query a
  = WebsocketResponse (RemoteData String Result) a

data BottomPanelView
  = CurrentStateView

derive instance eqBottomPanelView :: Eq BottomPanelView

derive instance genericBottomPanelView :: Generic BottomPanelView _

instance showBottomPanelView :: Show BottomPanelView where
  show = genericShow
