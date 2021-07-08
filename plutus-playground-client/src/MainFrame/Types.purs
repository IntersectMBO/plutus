module MainFrame.Types
  ( State(..)
  , View(..)
  , ChainSlot
  , Blockchain
  , WebData
  , WebCompilationResult
  , WebEvaluationResult
  , SimulatorAction
  , Query
  , HAction(..)
  , WalletEvent(..)
  , DragAndDropEventType(..)
  , ChildSlots
  ) where

import Analytics (class IsEvent, defaultEvent)
import Auth (AuthStatus)
import Chain.Types (Action(..))
import Chain.Types as Chain
import Clipboard as Clipboard
import Cursor (Cursor)
import Data.Either (Either)
import Data.Generic.Rep (class Generic)
import Data.Maybe (Maybe(..))
import Data.Newtype (class Newtype)
import Data.NonEmpty ((:|))
import Editor.Types as Editor
import Gist (Gist)
import Gists.Types (GistAction(..))
import Halogen as H
import Halogen.Chartist as Chartist
import Halogen.Monaco as Monaco
import Language.Haskell.Interpreter (InterpreterError, InterpreterResult)
import Network.RemoteData (RemoteData)
import Playground.Types (CompilationResult, ContractCall, ContractDemo, EvaluationResult, PlaygroundError, Simulation)
import Plutus.V1.Ledger.Tx (Tx)
import Prelude (class Eq, class Show, Unit, show, ($))
import Schema.Types (ActionEvent(..), FormArgument, SimulationAction(..))
import Servant.PureScript.Ajax (AjaxError)
import Test.QuickCheck.Arbitrary (class Arbitrary)
import Test.QuickCheck.Gen as Gen
import ValueEditor (ValueEvent(..))
import Web.HTML.Event.DragEvent (DragEvent)

newtype State
  = State
  { demoFilesMenuVisible :: Boolean
  , gistErrorPaneVisible :: Boolean
  , currentView :: View
  , contractDemos :: Array ContractDemo
  , currentDemoName :: Maybe String
  , editorState :: Editor.State
  , compilationResult :: WebCompilationResult
  , simulations :: Cursor Simulation
  , actionDrag :: Maybe Int
  , evaluationResult :: WebEvaluationResult
  , lastEvaluatedSimulation :: Maybe Simulation
  , authStatus :: WebData AuthStatus
  , createGistResult :: WebData Gist
  , gistUrl :: Maybe String
  , blockchainVisualisationState :: Chain.State
  }

derive instance newtypeState :: Newtype State _

data View
  = Editor
  | Simulations
  | Transactions

derive instance eqView :: Eq View

derive instance genericView :: Generic View _

instance arbitraryView :: Arbitrary View where
  arbitrary = Gen.elements (Editor :| [ Simulations, Transactions ])

instance showView :: Show View where
  show Editor = "Editor"
  show Simulations = "Simulation"
  show Transactions = "Transactions"

type ChainSlot
  = Array Tx

type Blockchain
  = Array ChainSlot

type WebData
  = RemoteData AjaxError

type WebCompilationResult
  = WebData (Either InterpreterError (InterpreterResult CompilationResult))

type WebEvaluationResult
  = WebData (Either PlaygroundError EvaluationResult)

-- this synonym is defined in playground-common/src/Playground/Types.hs
type SimulatorAction
  = ContractCall FormArgument

data Query a

data HAction
  = Init
  | Mounted
  -- SubEvents.
  | ActionDragAndDrop Int DragAndDropEventType DragEvent
  | HandleBalancesChartMessage Chartist.Message
  -- Gist support.
  | CheckAuthStatus
  | GistAction GistAction
  -- Demo files menu.
  | ToggleDemoFilesMenu
  -- Tabs.
  | ChangeView View
  -- Editor.
  | EditorAction Editor.Action
  | CompileProgram
  -- Simulations.
  | LoadScript String
  | AddSimulationSlot
  | SetSimulationSlot Int
  | RemoveSimulationSlot Int
  -- Wallets.
  | ModifyWallets WalletEvent
  -- Actions.
  | ChangeSimulation SimulationAction
  | EvaluateActions
  -- Chain.
  | ChainAction (Chain.Action)

data WalletEvent
  = AddWallet
  | RemoveWallet Int
  | ModifyBalance Int ValueEvent

data DragAndDropEventType
  = DragStart
  | DragEnd
  | DragEnter
  | DragOver
  | DragLeave
  | Drop

instance showDragAndDropEventType :: Show DragAndDropEventType where
  show DragStart = "DragStart"
  show DragEnd = "DragEnd"
  show DragEnter = "DragEnter"
  show DragOver = "DragOver"
  show DragLeave = "DragLeave"
  show Drop = "Drop"

type ChildSlots
  = ( editorSlot :: H.Slot Monaco.Query Monaco.Message Unit
    , balancesChartSlot :: H.Slot Chartist.Query Chartist.Message Unit
    )

-- | Here we decide which top-level queries to track as GA events, and
-- how to classify them.
instance actionIsEvent :: IsEvent HAction where
  toEvent Init = Nothing
  toEvent Mounted = Just $ defaultEvent "Mounted"
  toEvent (EditorAction (Editor.HandleDropEvent _)) = Just $ defaultEvent "DropScript"
  toEvent (EditorAction action) = Just $ (defaultEvent "ConfigureEditor")
  toEvent CompileProgram = Just $ defaultEvent "CompileProgram"
  toEvent (HandleBalancesChartMessage _) = Nothing
  toEvent CheckAuthStatus = Nothing
  toEvent (GistAction PublishOrUpdateGist) = Just $ (defaultEvent "Publish") { category = Just "Gist" }
  toEvent (GistAction (SetGistUrl _)) = Nothing
  toEvent (GistAction LoadGist) = Just $ (defaultEvent "LoadGist") { category = Just "Gist" }
  toEvent (GistAction (AjaxErrorPaneAction _)) = Nothing
  toEvent ToggleDemoFilesMenu = Nothing
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
  toEvent (ChangeSimulation (PopulateAction _ _)) = Just $ (defaultEvent "PopulateAction") { category = Just "Action" }
  toEvent (ChangeSimulation (ModifyActions (AddAction _))) = Just $ (defaultEvent "AddAction") { category = Just "Action" }
  toEvent (ChangeSimulation (ModifyActions (AddWaitAction _))) = Just $ (defaultEvent "AddWaitAction") { category = Just "Action" }
  toEvent (ChangeSimulation (ModifyActions (RemoveAction _))) = Just $ (defaultEvent "RemoveAction") { category = Just "Action" }
  toEvent (ChangeSimulation (ModifyActions (SetPayToWalletValue _ _))) = Just $ (defaultEvent "SetPayToWalletValue") { category = Just "Action" }
  toEvent (ChangeSimulation (ModifyActions (SetPayToWalletRecipient _ _))) = Just $ (defaultEvent "SetPayToWalletRecipient") { category = Just "Action" }
  toEvent (ChangeSimulation (ModifyActions (SetWaitTime _ _))) = Just $ (defaultEvent "SetWaitTime") { category = Just "Action" }
  toEvent (ChangeSimulation (ModifyActions (SetWaitUntilTime _ _))) = Just $ (defaultEvent "SetWaitUntilTime") { category = Just "Action" }
  toEvent (ChainAction (FocusTx (Just _))) = Just $ (defaultEvent "BlockchainFocus") { category = Just "Transaction" }
  toEvent (ChainAction (FocusTx Nothing)) = Nothing
  toEvent (ChainAction (ClipboardAction (Clipboard.CopyToClipboard _))) = Just $ (defaultEvent "ClipboardAction") { category = Just "CopyToClipboard" }
