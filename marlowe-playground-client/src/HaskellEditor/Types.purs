module HaskellEditor.Types where

import Prelude
import Analytics (class IsEvent, Event)
import Analytics as A
import Data.Either (Either(..))
import Data.Lens (Getter', Lens', Fold', _Right, to)
import Data.Lens.Record (prop)
import Data.Maybe (Maybe(..))
import Data.Symbol (SProxy(..))
import Halogen.Monaco (KeyBindings(..))
import Halogen.Monaco as Monaco
import Language.Haskell.Interpreter (InterpreterError, InterpreterResult, _InterpreterResult)
import Marlowe.Parser (parseContract)
import Network.RemoteData (RemoteData(..), _Success)
import Simulation.Types (WebData)
import Text.Pretty (pretty)

data Action
  = Compile
  | ChangeKeyBindings KeyBindings
  | HandleEditorMessage Monaco.Message
  | ShowBottomPanel Boolean
  | SendResultToSimulator
  | SendResultToBlockly
  | InitHaskellProject String
  | MarkProjectAsSaved

defaultEvent :: String -> Event
defaultEvent s = A.defaultEvent $ "Haskell." <> s

instance actionIsEvent :: IsEvent Action where
  toEvent Compile = Just $ defaultEvent "Compile"
  toEvent (ChangeKeyBindings _) = Just $ defaultEvent "ChangeKeyBindings"
  toEvent (HandleEditorMessage _) = Just $ defaultEvent "HandleEditorMessage"
  toEvent (ShowBottomPanel _) = Just $ defaultEvent "ShowBottomPanel"
  toEvent SendResultToSimulator = Just $ defaultEvent "SendResultToSimulator"
  toEvent SendResultToBlockly = Just $ defaultEvent "SendResultToBlockly"
  toEvent (InitHaskellProject _) = Just $ defaultEvent "InitHaskellProject"
  toEvent MarkProjectAsSaved = Just $ defaultEvent "MarkProjectAsSaved"

type State
  = { keybindings :: KeyBindings
    , compilationResult :: WebData (Either InterpreterError (InterpreterResult String))
    , showBottomPanel :: Boolean
    , hasUnsavedChanges :: Boolean
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

_showBottomPanel :: Lens' State Boolean
_showBottomPanel = prop (SProxy :: SProxy "showBottomPanel")

initialState :: State
initialState =
  { keybindings: DefaultBindings
  , compilationResult: NotAsked
  , showBottomPanel: true
  , hasUnsavedChanges: false
  }
