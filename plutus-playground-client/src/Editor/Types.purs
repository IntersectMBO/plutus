module Editor.Types where

import Data.Either (Either)
import Data.Enum (enumFromTo)
import Data.Lens (Lens')
import Data.Lens.Iso.Newtype (_Newtype)
import Data.Lens.Record (prop)
import Data.Newtype (class Newtype)
import Data.Symbol (SProxy(..))
import Halogen.Monaco (KeyBindings(..))
import Halogen.Monaco (Message) as Monaco
import Language.Haskell.Interpreter (InterpreterError, InterpreterResult)
import LocalStorage (Key(..))
import Monaco (IPosition)
import Network.RemoteData (RemoteData)
import Prelude (bottom, top, (<<<))
import Servant.PureScript.Ajax (AjaxError)
import Web.HTML.Event.DragEvent (DragEvent)

data Action
  = Init
  | HandleEditorMessage Monaco.Message
  | HandleDragEvent DragEvent
  | HandleDropEvent DragEvent
  | ScrollTo IPosition
  | SetKeyBindings KeyBindings
  | ToggleFeedbackPane

------------------------------------------------------------
allKeyBindings :: Array KeyBindings
allKeyBindings = enumFromTo bottom top

readKeyBindings :: String -> KeyBindings
readKeyBindings "Emacs" = Emacs

readKeyBindings "Vim" = Vim

readKeyBindings _ = DefaultBindings

------------------------------------------------------------
newtype State
  = State
  { keyBindings :: KeyBindings
  , feedbackPaneMinimised :: Boolean
  }

derive instance newtypeState :: Newtype State _

------------------------------------------------------------
keybindingsLocalStorageKey :: Key
keybindingsLocalStorageKey = Key "EditorPreferences.KeyBindings"

type CompilationState a
  = RemoteData AjaxError (Either InterpreterError (InterpreterResult a))

_warnings :: forall s a. Lens' { warnings :: a | s } a
_warnings = prop (SProxy :: SProxy "warnings")

_keyBindings :: Lens' State KeyBindings
_keyBindings = _Newtype <<< prop (SProxy :: SProxy "keyBindings")

_feedbackPaneMinimised :: Lens' State Boolean
_feedbackPaneMinimised = _Newtype <<< prop (SProxy :: SProxy "feedbackPaneMinimised")
