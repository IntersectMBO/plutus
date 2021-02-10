module Editor.Lenses
  ( _warnings
  , _keyBindings
  , _feedbackPaneMinimised
  , _lastCompiledCode
  , _currentCodeIsCompiled
  , _feedbackPaneDragStart
  , _feedbackPaneExtend
  , _feedbackPanePreviousExtend
  ) where

import Data.Lens (Lens')
import Data.Lens.Iso.Newtype (_Newtype)
import Data.Lens.Record (prop)
import Data.Maybe (Maybe)
import Data.Symbol (SProxy(..))
import Editor.Types (State)
import Halogen.Monaco (KeyBindings)
import Language.Haskell.Interpreter (SourceCode)
import Prelude ((<<<))

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
