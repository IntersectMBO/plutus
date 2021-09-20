module JavascriptEditor.Types where

import Prelude
import Analytics (class IsEvent, Event)
import Analytics as A
import BottomPanel.Types as BottomPanel
import Data.BigInteger (BigInteger)
import Data.Either (Either(..))
import Data.Generic.Rep (class Generic)
import Data.Generic.Rep.Show (genericShow)
import Data.Lens (Getter', Lens', Prism', Fold', prism, to, (^.))
import Data.Lens.Record (prop)
import Data.Maybe (Maybe(..))
import Data.Symbol (SProxy(..))
import Halogen.Monaco (KeyBindings(..))
import Halogen.Monaco as Monaco
import Language.Javascript.Interpreter (_result)
import Language.Javascript.Interpreter as JS
import Marlowe.Extended (Contract)
import Marlowe.Extended.Metadata (MetadataHintInfo)
import Marlowe.Template (IntegerTemplateType)
import MetadataTab.Types (MetadataAction, showConstructor)
import StaticAnalysis.Types (AnalysisState, initAnalysisState)
import Text.Pretty (pretty)

data CompilationState
  = NotCompiled
  | Compiling
  | CompilationError JS.CompilationError
  | CompiledSuccessfully (JS.InterpreterResult Contract)

_CompiledSuccessfully :: Prism' CompilationState (JS.InterpreterResult Contract)
_CompiledSuccessfully = prism CompiledSuccessfully unwrap
  where
  unwrap (CompiledSuccessfully x) = Right x

  unwrap y = Left y

_Pretty :: Getter' Contract String
_Pretty = to (show <<< pretty)

_ContractString :: forall r. Monoid r => Fold' r State String
_ContractString = _compilationResult <<< _CompiledSuccessfully <<< _result <<< _Pretty

data Action
  = Compile
  | ChangeKeyBindings KeyBindings
  | HandleEditorMessage Monaco.Message
  | BottomPanelAction (BottomPanel.Action BottomPanelView Action)
  | SendResultToSimulator
  | InitJavascriptProject MetadataHintInfo String
  | SetIntegerTemplateParam IntegerTemplateType String BigInteger
  | AnalyseContract
  | AnalyseReachabilityContract
  | AnalyseContractForCloseRefund
  | ClearAnalysisResults
  | MetadataAction MetadataAction

defaultEvent :: String -> Event
defaultEvent s = A.defaultEvent $ "Javascript." <> s

instance actionIsEvent :: IsEvent Action where
  toEvent Compile = Just $ defaultEvent "Compile"
  toEvent (ChangeKeyBindings _) = Just $ defaultEvent "ChangeKeyBindings"
  toEvent (HandleEditorMessage _) = Just $ defaultEvent "HandleEditorMessage"
  toEvent (BottomPanelAction action) = A.toEvent action
  toEvent SendResultToSimulator = Just $ defaultEvent "SendResultToSimulator"
  toEvent (InitJavascriptProject _ _) = Just $ defaultEvent "InitJavascriptProject"
  toEvent (SetIntegerTemplateParam _ _ _) = Just $ defaultEvent "SetIntegerTemplateParam"
  toEvent AnalyseContract = Just $ defaultEvent "AnalyseContract"
  toEvent AnalyseReachabilityContract = Just $ defaultEvent "AnalyseReachabilityContract"
  toEvent AnalyseContractForCloseRefund = Just $ defaultEvent "AnalyseContractForCloseRefund"
  toEvent ClearAnalysisResults = Just $ defaultEvent "ClearAnalysisResults"
  toEvent (MetadataAction action) = Just $ (defaultEvent "MetadataAction") { label = Just $ showConstructor action }

type DecorationIds
  = { topDecorationId :: String
    , bottomDecorationId :: String
    }

_topDecorationId :: Lens' DecorationIds String
_topDecorationId = prop (SProxy :: SProxy "topDecorationId")

_bottomDecorationId :: Lens' DecorationIds String
_bottomDecorationId = prop (SProxy :: SProxy "bottomDecorationId")

type State
  = { keybindings :: KeyBindings
    , bottomPanelState :: BottomPanel.State BottomPanelView
    , compilationResult :: CompilationState
    , decorationIds :: Maybe DecorationIds
    , metadataHintInfo :: MetadataHintInfo
    , analysisState :: AnalysisState
    , editorReady :: Boolean
    }

_keybindings :: Lens' State KeyBindings
_keybindings = prop (SProxy :: SProxy "keybindings")

_compilationResult :: Lens' State CompilationState
_compilationResult = prop (SProxy :: SProxy "compilationResult")

_decorationIds :: Lens' State (Maybe DecorationIds)
_decorationIds = prop (SProxy :: SProxy "decorationIds")

_bottomPanelState :: Lens' State (BottomPanel.State BottomPanelView)
_bottomPanelState = prop (SProxy :: SProxy "bottomPanelState")

_metadataHintInfo :: Lens' State MetadataHintInfo
_metadataHintInfo = prop (SProxy :: SProxy "metadataHintInfo")

_analysisState :: Lens' State AnalysisState
_analysisState = prop (SProxy :: SProxy "analysisState")

_editorReady :: Lens' State Boolean
_editorReady = prop (SProxy :: SProxy "editorReady")

isCompiling :: State -> Boolean
isCompiling state = case state ^. _compilationResult of
  Compiling -> true
  _ -> false

initialState :: State
initialState =
  { keybindings: DefaultBindings
  , bottomPanelState: BottomPanel.initialState MetadataView
  , compilationResult: NotCompiled
  , decorationIds: Nothing
  , metadataHintInfo: mempty
  , analysisState: initAnalysisState
  , editorReady: false
  }

data BottomPanelView
  = StaticAnalysisView
  | ErrorsView
  | GeneratedOutputView
  | MetadataView

derive instance eqBottomPanelView :: Eq BottomPanelView

derive instance genericBottomPanelView :: Generic BottomPanelView _

instance showBottomPanelView :: Show BottomPanelView where
  show = genericShow
