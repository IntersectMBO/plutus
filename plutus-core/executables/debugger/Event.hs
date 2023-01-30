{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}

-- | Handler of debugger events.
module Event where

import Annotation
import Types
import UntypedPlutusCore.Evaluation.Machine.Cek.Debug.Driver qualified as D

import Brick.Focus qualified as B
import Brick.Main qualified as B
import Brick.Types qualified as B
import Brick.Widgets.Edit qualified as BE
import Control.Concurrent.MVar
import Control.Monad.State
import Data.MonoTraversable
import Graphics.Vty qualified as Vty
import Lens.Micro

type Breakpoints = [Breakpoint]
data Breakpoint = UplcBP SourcePos
                | TxBP SourcePos
data DAnn = DAnn
    { uplcAnn :: SourcePos
    , txAnn   :: SrcSpans
    }

instance D.Breakpointable DAnn Breakpoints where
    hasBreakpoints ann = any breakpointFired
        where
          breakpointFired :: Breakpoint -> Bool
          breakpointFired = \case
              UplcBP p -> sourceLine p == sourceLine (uplcAnn ann)
              TxBP p   -> oany (lineInSrcSpan $ sourceLine p) $ txAnn ann

handleDebuggerEvent :: MVar (D.Cmd Breakpoints)
                    -> B.BrickEvent ResourceName e
                    -> B.EventM ResourceName DebuggerState ()
handleDebuggerEvent driverMailbox bev@(B.VtyEvent ev) = do
    focusRing <- gets (^. dsFocusRing)
    let handleEditorEvent = case B.focusGetCurrent focusRing of
            Just EditorUplc ->
                B.zoom dsUplcEditor $ BE.handleEditorEvent bev
            Just EditorSource ->
                B.zoom dsSourceEditor $ BE.handleEditorEvent bev
            Just EditorReturnValue ->
                B.zoom dsReturnValueEditor $ BE.handleEditorEvent bev
            Just EditorCekState ->
                B.zoom dsCekStateEditor $ BE.handleEditorEvent bev
            _ -> pure ()
    keyBindingsMode <- gets (^. dsKeyBindingsMode)
    case ev of
        Vty.EvKey{}
            | KeyBindingsShown <- keyBindingsMode ->
                modify' $ set dsKeyBindingsMode KeyBindingsHidden
        Vty.EvKey (Vty.KChar '?') [] ->
            modify' $ set dsKeyBindingsMode KeyBindingsShown
        Vty.EvKey Vty.KEsc [] -> B.halt
        Vty.EvKey (Vty.KChar 's') [] -> do
          _success <- liftIO $ tryPutMVar driverMailbox D.Step
          -- MAYBE: when not success we could have a dialog show up
          -- saying that the debugger seems to be stuck
          -- and an option to kill its thread (cek) and reload the program?
          modify' $ \st ->
            -- Stepping. Currently it highlights one line at a time.
            let highlightNextLine = \case
                    Nothing ->
                        Just (HighlightSpan (B.Location (1, 1)) Nothing)
                    Just (HighlightSpan (B.Location (r, c)) _) ->
                        Just (HighlightSpan (B.Location (r + 1, c)) Nothing)
             in st & dsUplcHighlight %~ highlightNextLine

        Vty.EvKey (Vty.KChar '\t') [] -> modify' $ \st ->
            st & dsFocusRing %~ B.focusNext
        Vty.EvKey Vty.KBackTab [] -> modify' $ \st ->
            st & dsFocusRing %~ B.focusPrev
        Vty.EvKey Vty.KUp [Vty.MCtrl] -> modify' $ \st ->
            st & dsVLimitBottomEditors %~ (+ 1)
        Vty.EvKey Vty.KDown [Vty.MCtrl] -> modify' $ \st ->
            st & dsVLimitBottomEditors %~ (\x -> x - 1)
        Vty.EvKey Vty.KUp [] -> handleEditorEvent
        Vty.EvKey Vty.KDown [] -> handleEditorEvent
        Vty.EvKey Vty.KLeft [] -> handleEditorEvent
        Vty.EvKey Vty.KRight [] -> handleEditorEvent
        Vty.EvKey (Vty.KChar _) [] ->
            -- This disables editing the text, making the editors read-only.
            pure ()
        _ -> handleEditorEvent
handleDebuggerEvent _ _ = pure ()
