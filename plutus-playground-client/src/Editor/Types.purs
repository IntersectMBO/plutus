module Editor.Types where

import Data.Enum (enumFromTo)
import Data.Lens (Lens')
import Data.Lens.Iso.Newtype (_Newtype)
import Data.Lens.Record (prop)
import Data.Maybe (Maybe)
import Data.Newtype (class Newtype)
import Data.Symbol (SProxy(..))
import Halogen.Monaco (KeyBindings(..))
import Halogen.Monaco (Message) as Monaco
import Language.Haskell.Interpreter (SourceCode)
import LocalStorage (Key(..))
import Monaco (IPosition)
import Prelude (bottom, top, (<<<))
import Web.HTML.Event.DragEvent (DragEvent)

data Action
  = Init
  | HandleEditorMessage Monaco.Message
  | HandleDragEvent DragEvent
  | HandleDropEvent DragEvent
  | ScrollTo IPosition
  | SetKeyBindings KeyBindings
  | ToggleFeedbackPane
  | SetFeedbackPaneDragStart (Maybe Int)
  | ClearFeedbackPaneDragStart
  | FixFeedbackPaneExtend Int

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
  , lastCompiledCode :: Maybe SourceCode
  , currentCodeIsCompiled :: Boolean
  , feedbackPaneDragStart :: Maybe Int
  , feedbackPaneExtend :: Int
  , feedbackPanePreviousExtend :: Int
  }

derive instance newtypeState :: Newtype State _

------------------------------------------------------------
keybindingsLocalStorageKey :: Key
keybindingsLocalStorageKey = Key "EditorPreferences.KeyBindings"

_warnings :: forall s a. Lens' { warnings :: a | s } a
_warnings = prop (SProxy :: SProxy "warnings")

_keyBindings :: Lens' State KeyBindings
_keyBindings = _Newtype <<< prop (SProxy :: SProxy "keyBindings")

_feedbackPaneMinimised :: Lens' State Boolean
_feedbackPaneMinimised = _Newtype <<< prop (SProxy :: SProxy "feedbackPaneMinimised")

_lastCompiledCode :: Lens' State (Maybe SourceCode)
_lastCompiledCode = _Newtype <<< prop (SProxy :: SProxy "lastCompiledCode")

_currentCodeIsCompiled :: Lens' State Boolean
_currentCodeIsCompiled = _Newtype <<< prop (SProxy :: SProxy "currentCodeIsCompiled")

_feedbackPaneDragStart :: Lens' State (Maybe Int)
_feedbackPaneDragStart = _Newtype <<< prop (SProxy :: SProxy "feedbackPaneDragStart")

_feedbackPaneExtend :: Lens' State Int
_feedbackPaneExtend = _Newtype <<< prop (SProxy :: SProxy "feedbackPaneExtend")

_feedbackPanePreviousExtend :: Lens' State Int
_feedbackPanePreviousExtend = _Newtype <<< prop (SProxy :: SProxy "feedbackPanePreviousExtend")
