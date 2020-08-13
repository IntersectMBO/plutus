module HaskellEditor.Types where

import Prelude
import API (RunResult)
import Analytics (class IsEvent, Event)
import Analytics as A
import Data.Json.JsonEither (JsonEither)
import Data.Lens (Lens')
import Data.Lens.Record (prop)
import Data.Maybe (Maybe(..))
import Data.Symbol (SProxy(..))
import Halogen.Monaco (KeyBindings(..))
import Halogen.Monaco as Monaco
import Language.Haskell.Interpreter (InterpreterError, InterpreterResult)
import Network.RemoteData (RemoteData(..))
import Simulation.Types (WebData)

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

type State
  = { activeDemo :: String
    , keybindings :: KeyBindings
    , compilationResult :: WebData (JsonEither InterpreterError (InterpreterResult RunResult))
    , showBottomPanel :: Boolean
    }

_activeHaskellDemo :: Lens' State String
_activeHaskellDemo = prop (SProxy :: SProxy "activeDemo")

_haskellEditorKeybindings :: Lens' State KeyBindings
_haskellEditorKeybindings = prop (SProxy :: SProxy "keybindings")

_compilationResult :: Lens' State (WebData (JsonEither InterpreterError (InterpreterResult RunResult)))
_compilationResult = prop (SProxy :: SProxy "compilationResult")

_showBottomPanel :: Lens' State Boolean
_showBottomPanel = prop (SProxy :: SProxy "showBottomPanel")

initialState :: State
initialState =
  { activeDemo: mempty
  , keybindings: DefaultBindings
  , compilationResult: NotAsked
  , showBottomPanel: true
  }
