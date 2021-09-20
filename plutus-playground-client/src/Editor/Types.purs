module Editor.Types
  ( State(..)
  , Action(..)
  , allKeyBindings
  , readKeyBindings
  ) where

import Data.Enum (enumFromTo)
import Data.Maybe (Maybe)
import Data.Newtype (class Newtype)
import Halogen.Monaco (KeyBindings(..), Message)
import Language.Haskell.Interpreter (SourceCode)
import Monaco (IPosition)
import Prelude (bottom, top)
import Web.HTML.Event.DragEvent (DragEvent)
import Web.UIEvent.MouseEvent (MouseEvent)

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

data Action
  = Init
  | HandleEditorMessage Message
  | HandleDragEvent DragEvent
  | HandleDropEvent DragEvent
  | ScrollTo IPosition
  | SetKeyBindings KeyBindings
  | ToggleFeedbackPane
  | SetFeedbackPaneDragStart MouseEvent
  | ClearFeedbackPaneDragStart
  | FixFeedbackPaneExtend Int

allKeyBindings :: Array KeyBindings
allKeyBindings = enumFromTo bottom top

readKeyBindings :: String -> KeyBindings
readKeyBindings "Emacs" = Emacs

readKeyBindings "Vim" = Vim

readKeyBindings _ = DefaultBindings
