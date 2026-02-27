{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TemplateHaskell #-}

-- | Debugger TUI Types.
module Debugger.TUI.Types where

import PlutusCore.Annotation
import PlutusCore.Evaluation.Machine.ExBudget
import UntypedPlutusCore as UPLC
import UntypedPlutusCore.Evaluation.Machine.SteppableCek.DebugDriver qualified as D
import UntypedPlutusCore.Evaluation.Machine.SteppableCek.Internal

import Brick.Focus qualified as B
import Brick.Types qualified as B
import Brick.Widgets.Edit qualified as BE
import Data.MonoTraversable
import Data.Text (Text)
import Lens.Micro.TH
import Text.Megaparsec

type Breakpoints = [Breakpoint]

data Breakpoint
  = UplcBP SourcePos
  | TxBP SourcePos

{-| Annotation used in the debugger. Contains source locations for the UPLC program
and the source program. -}
data DAnn = DAnn
  { uplcAnn :: SrcSpan
  , txAnn :: SrcSpans
  }

instance D.Breakpointable DAnn Breakpoints where
  hasBreakpoints ann = any breakpointFired
    where
      breakpointFired :: Breakpoint -> Bool
      breakpointFired = \case
        UplcBP p -> unPos (sourceLine p) == srcSpanSLine (uplcAnn ann)
        TxBP p -> oany (lineInSrcSpan $ sourceLine p) $ txAnn ann

data BudgetData = BudgetData
  { _budgetSpent :: ExBudget
  , _budgetRemaining :: Maybe ExBudget
  }
makeLenses ''BudgetData

-- | The custom events that can arrive at our brick mailbox.
data CustomBrickEvent
  = {-| the driver passes a new cek state to the brick client
    this should mean that the brick client should update its tui -}
    UpdateClientEvent BudgetData (CekState DefaultUni DefaultFun DAnn)
  | -- | the driver logged some text, the brick client can decide to show it in the tui
    DriverLogEvent Text
  | -- | the underlying cek machine emitted some text (using a trace or other builtin)
    CekEmitEvent Text
  | -- | the underlying cek machine errored (either by call to Error, builtin or type failure)
    CekErrorEvent BudgetData (CekEvaluationException NamedDeBruijn DefaultUni DefaultFun)

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
  | EditorLogs
  deriving stock (Eq, Ord, Show)

data DebuggerState = DebuggerState
  { _dsKeyBindingsMode :: KeyBindingsMode
  , _dsFocusRing :: B.FocusRing ResourceName
  -- ^ Controls which window is in focus.
  , _dsUplcEditor :: BE.Editor Text ResourceName
  , _dsUplcHighlight :: Maybe HighlightSpan
  , _dsSourceEditor :: Maybe (BE.Editor Text ResourceName)
  , _dsSourceHighlight :: Maybe HighlightSpan
  , _dsReturnValueEditor :: BE.Editor Text ResourceName
  , _dsLogsEditor :: BE.Editor Text ResourceName
  , _dsVLimitBottomEditors :: Int
  -- ^ Controls the height limit of the bottom windows.
  , _dsHLimitRightEditors :: Int
  -- ^ Controls the width limit of the right windows.
  , _dsBudgetData :: BudgetData
  }

makeLenses ''DebuggerState
