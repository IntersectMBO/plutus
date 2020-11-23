module JavascriptEditor.Types where

import Prelude
import Analytics (class IsEvent, Event)
import Analytics as A
import Data.Either (Either(..))
import Data.Lens (Getter', Lens', Prism', Fold', prism, to)
import Data.Lens.Record (prop)
import Data.Maybe (Maybe(..))
import Data.Symbol (SProxy(..))
import Halogen.Monaco (KeyBindings(..))
import Halogen.Monaco as Monaco
import Language.Javascript.Interpreter (_result)
import Language.Javascript.Interpreter as JS
import Marlowe.Semantics (Contract)
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
  | LoadScript String
  | HandleEditorMessage Monaco.Message
  | ShowBottomPanel Boolean
  | SendResultToSimulator
  | SendResultToBlockly

defaultEvent :: String -> Event
defaultEvent s = A.defaultEvent $ "Haskell." <> s

instance actionIsEvent :: IsEvent Action where
  toEvent Compile = Just $ defaultEvent "Compile"
  toEvent (ChangeKeyBindings _) = Just $ defaultEvent "ChangeKeyBindings"
  toEvent (LoadScript _) = Just $ defaultEvent "LoadScript"
  toEvent (HandleEditorMessage _) = Just $ defaultEvent "HandleEditorMessage"
  toEvent (ShowBottomPanel _) = Just $ defaultEvent "ShowBottomPanel"
  toEvent SendResultToSimulator = Just $ defaultEvent "SendResultToSimulator"
  toEvent SendResultToBlockly = Just $ defaultEvent "SendResultToBlockly"

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
    , compilationResult :: CompilationState
    , showBottomPanel :: Boolean
    , decorationIds :: Maybe DecorationIds
    }

_keybindings :: Lens' State KeyBindings
_keybindings = prop (SProxy :: SProxy "keybindings")

_compilationResult :: Lens' State CompilationState
_compilationResult = prop (SProxy :: SProxy "compilationResult")

_showBottomPanel :: Lens' State Boolean
_showBottomPanel = prop (SProxy :: SProxy "showBottomPanel")

_decorationIds :: Lens' State (Maybe DecorationIds)
_decorationIds = prop (SProxy :: SProxy "decorationIds")

initialState :: State
initialState =
  { keybindings: DefaultBindings
  , compilationResult: NotCompiled
  , showBottomPanel: true
  , decorationIds: Nothing
  }
