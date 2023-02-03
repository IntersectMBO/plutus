{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE TupleSections         #-}

-- | Handler of debugger events.
module Event where

import Annotation
import PlutusCore.Pretty qualified as PLC
import Types
import UntypedPlutusCore qualified as UPLC
import UntypedPlutusCore.Evaluation.Machine.Cek.Debug.Driver qualified as D
import UntypedPlutusCore.Evaluation.Machine.Cek.Debug.Internal

import Brick.Focus qualified as B
import Brick.Main qualified as B
import Brick.Types qualified as B
import Brick.Widgets.Edit qualified as BE
import Control.Concurrent.MVar
import Control.Monad.State
import Graphics.Vty qualified as Vty
import Lens.Micro
import Prettyprinter

handleDebuggerEvent :: MVar (D.Cmd Breakpoints)
                    -> B.BrickEvent ResourceName CustomBrickEvent
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
          -- MAYBE: when not success we could have a dialog show up
          -- saying that the debugger seems to be stuck
          -- and an option to kill its thread (cek) and reload the program?
          _success <- liftIO $ tryPutMVar driverMailbox D.Step
          pure ()
        Vty.EvKey (Vty.KChar '\t') [] -> modify' $ \st ->
            st & dsFocusRing %~ B.focusNext
        Vty.EvKey Vty.KBackTab [] -> modify' $ \st ->
            st & dsFocusRing %~ B.focusPrev
        Vty.EvKey Vty.KUp [Vty.MCtrl] -> modify' $ \st ->
            st & dsVLimitBottomEditors %~ (+ 1)
        Vty.EvKey Vty.KDown [Vty.MCtrl] -> modify' $ \st ->
            st & dsVLimitBottomEditors %~ (\x -> x - 1)
        Vty.EvKey Vty.KLeft [Vty.MCtrl] -> modify' $ \st ->
            st & dsHLimitRightEditors %~ (+ 1)
        Vty.EvKey Vty.KRight [Vty.MCtrl] -> modify' $ \st ->
            st & dsHLimitRightEditors %~ (\x -> x - 1)
        Vty.EvKey Vty.KUp [] -> handleEditorEvent
        Vty.EvKey Vty.KDown [] -> handleEditorEvent
        Vty.EvKey Vty.KLeft [] -> handleEditorEvent
        Vty.EvKey Vty.KRight [] -> handleEditorEvent
        Vty.EvKey (Vty.KChar _) [] ->
            -- This disables editing the text, making the editors read-only.
            pure ()
        _ -> handleEditorEvent
handleDebuggerEvent _driverMailbox (B.AppEvent (UpdateClientEvent cekState)) = do
    let uplcHighlight = do
            uplcSpan <- uplcAnn <$> case cekState of
                Computing _ _ _ t -> Just (UPLC.termAnn t)
                Returning _ ctx _ -> contextAnn ctx
                _                 -> Nothing
            pure HighlightSpan
                { _hcSLoc = B.Location (srcSpanSLine uplcSpan, srcSpanSCol uplcSpan),
                  _hcELoc = Just $ B.Location (srcSpanELine uplcSpan, srcSpanECol uplcSpan)
                }
    modify' $ \st -> case cekState of
        Computing{} ->
            st & dsUplcHighlight .~ uplcHighlight
               -- Clear the return value editor.
               & dsReturnValueEditor .~
                BE.editorText
                    EditorReturnValue
                    Nothing
                    mempty
        Returning _ _ v ->
            st & dsUplcHighlight .~ uplcHighlight
               & dsReturnValueEditor .~
                BE.editorText
                    EditorReturnValue
                    Nothing
                    (PLC.displayPlcDef (dischargeCekValue v))

        Terminating t ->
            st & dsUplcHighlight .~ Nothing
               & dsReturnValueEditor .~
                BE.editorText
                    EditorReturnValue
                    Nothing
                    (PLC.render $ vcat ["Evaluation Finished. Result:", line, PLC.prettyPlcDef t])
        Starting{} -> st
handleDebuggerEvent _ _ = pure ()
