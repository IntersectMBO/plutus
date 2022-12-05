{-# LANGUAGE TemplateHaskell #-}

module Types where

import Brick.Focus qualified as B
import Brick.Types qualified as B
import Brick.Widgets.Edit qualified as BE
import Data.Text (Text)
import Lens.Micro.TH

data KeyBindingsMode = KeyBindingsShown | KeyBindingsHidden
    deriving stock (Eq, Ord, Show)

-- | Highlight between two positions.
data HighlightSpan = HighlightSpan
    { _hcSLoc :: B.Location
    , _hcELoc :: Maybe B.Location
    -- ^ @Nothing@ means highlight till the end of the line
    }

data ResourceName
    = FileBrowserUplc
    | EditorUplc
    | EditorSource
    | EditorReturnValue
    | EditorCekState
    deriving stock (Eq, Ord, Show)

data DebuggerState = DebuggerState
    { _dsKeyBindingsMode     :: KeyBindingsMode
    , _dsFocusRing           :: B.FocusRing ResourceName
    -- ^ Controls which window is in focus.
    , _dsUplcEditor          :: BE.Editor Text ResourceName
    , _dsUplcHighlight       :: Maybe HighlightSpan
    , _dsSourceEditor        :: BE.Editor Text ResourceName
    , _dsReturnValueEditor   :: BE.Editor Text ResourceName
    , _dsCekStateEditor      :: BE.Editor Text ResourceName
    , _dsVLimitBottomEditors :: Int
    -- ^ Controls the height limit of the bottom windows.
    }

makeLenses ''DebuggerState
