module HaskellEditor.Types where

import Prelude
import Analytics (class IsEvent, Event)
import Analytics as A
import BottomPanel.Types as BottomPanel
import Data.Either (Either(..))
import Data.Generic.Rep (class Generic)
import Data.Generic.Rep.Show (genericShow)
import Data.Lens (Fold', Getter', Lens', _Right, has, to)
import Data.Lens.Record (prop)
import Data.Maybe (Maybe(..))
import Data.Symbol (SProxy(..))
import Halogen.Monaco (KeyBindings(..))
import Halogen.Monaco as Monaco
import Language.Haskell.Interpreter (InterpreterError, InterpreterResult, _InterpreterResult)
import Marlowe.Parser (parseContract)
import Network.RemoteData (RemoteData(..), _Loading, _Success)
import StaticAnalysis.Types (AnalysisExecutionState(..), AnalysisState)
import Text.Pretty (pretty)
import Types (WebData)

data Action
  = Init
  | Compile
  | ChangeKeyBindings KeyBindings
  | HandleEditorMessage Monaco.Message
  | BottomPanelAction (BottomPanel.Action BottomPanelView Action)
  | SendResultToSimulator
  | InitHaskellProject String
  | AnalyseContract
  | AnalyseReachabilityContract
  | AnalyseContractForCloseRefund

defaultEvent :: String -> Event
defaultEvent s = A.defaultEvent $ "Haskell." <> s

instance actionIsEvent :: IsEvent Action where
  toEvent Init = Just $ defaultEvent "Init"
  toEvent Compile = Just $ defaultEvent "Compile"
  toEvent (ChangeKeyBindings _) = Just $ defaultEvent "ChangeKeyBindings"
  toEvent (HandleEditorMessage _) = Just $ defaultEvent "HandleEditorMessage"
  toEvent (BottomPanelAction action) = A.toEvent action
  toEvent SendResultToSimulator = Just $ defaultEvent "SendResultToSimulator"
  toEvent (InitHaskellProject _) = Just $ defaultEvent "InitHaskellProject"
  toEvent AnalyseContract = Just $ defaultEvent "AnalyseContract"
  toEvent AnalyseReachabilityContract = Just $ defaultEvent "AnalyseReachabilityContract"
  toEvent AnalyseContractForCloseRefund = Just $ defaultEvent "AnalyseContractForCloseRefund"

type State
  = { keybindings :: KeyBindings
    , compilationResult :: WebData (Either InterpreterError (InterpreterResult String))
    , bottomPanelState :: BottomPanel.State BottomPanelView
    , analysisState :: AnalysisState
    }

_haskellEditorKeybindings :: Lens' State KeyBindings
_haskellEditorKeybindings = prop (SProxy :: SProxy "keybindings")

_compilationResult :: Lens' State (WebData (Either InterpreterError (InterpreterResult String)))
_compilationResult = prop (SProxy :: SProxy "compilationResult")

--- Language.Haskell.Interpreter is missing this ---
_result :: forall s a. Lens' { result :: a | s } a
_result = prop (SProxy :: SProxy "result")

_Pretty :: Getter' String String
_Pretty = to f
  where
  f ugly = case parseContract ugly of
    Right contract -> (show <<< pretty) contract
    Left _ -> ugly

_ContractString :: forall r. Monoid r => Fold' r State String
_ContractString = _compilationResult <<< _Success <<< _Right <<< _InterpreterResult <<< _result <<< _Pretty

_bottomPanelState :: Lens' State (BottomPanel.State BottomPanelView)
_bottomPanelState = prop (SProxy :: SProxy "bottomPanelState")

initialState :: State
initialState =
  { keybindings: DefaultBindings
  , compilationResult: NotAsked
  , bottomPanelState: BottomPanel.initialState GeneratedOutputView
  , analysisState:
      { templateContent: mempty
      , analysisExecutionState: NoneAsked
      }
  }

isCompiling :: State -> Boolean
isCompiling = has (_compilationResult <<< _Loading)

data BottomPanelView
  = StaticAnalysisView
  | ErrorsView
  | GeneratedOutputView

derive instance eqBottomPanelView :: Eq BottomPanelView

derive instance genericBottomPanelView :: Generic BottomPanelView _

instance showBottomPanelView :: Show BottomPanelView where
  show = genericShow
