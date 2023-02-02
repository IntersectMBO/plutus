{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}

-- | Handler of debugger events.
module Event where

import Annotation
import PlutusCore qualified as PLC
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
import Data.Text qualified as Text
import Graphics.Vty qualified as Vty
import Lens.Micro
import Text.Megaparsec

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
    let mHighlightedTerm = case cekState of
            Computing _ _ _ t -> Just $ t
            Returning _ ctx v -> do
                ann <- contextAnn ctx
                pure $ const ann <$> dischargeCekValue v
            _ -> Nothing
        uplcHighlight = do
            highlightedTerm <- mHighlightedTerm
            let uplcPos = uplcAnn $ UPLC.termAnn highlightedTerm
            pure $ mkUplcSpan uplcPos highlightedTerm
    modify' $ \st -> case cekState of
        Computing{} ->
            st & dsUplcHighlight .~ uplcHighlight
               & dsReturnValueEditor .~
                BE.editorText
                    EditorReturnValue
                    Nothing
                    ""
        Returning _ _ v ->
            let vtag = case v of
                    VCon{}     -> "VCon"
                    VDelay{}   -> "VDelay"
                    VLamAbs{}  -> "VLamAbs"
                    VBuiltin{} -> "VBuiltin"
            in st & dsUplcHighlight .~ uplcHighlight
                  & dsReturnValueEditor .~
                BE.editorText
                    EditorReturnValue
                    Nothing
                    (vtag <> ": " <> PLC.displayPlcDef (dischargeCekValue v))

        Terminating t ->
            st & dsUplcHighlight .~ Nothing
               & dsReturnValueEditor .~
                BE.editorText
                    EditorReturnValue
                    Nothing
                    ("Evaluation Finished. Result: \n\n" <> PLC.displayPlcDef t)
        Starting{} -> st
handleDebuggerEvent _ _ = pure ()

-- | Attempt to highlight the first token of a Term. This is a temporary workaround.
--
-- Ideally we want to highlight the entire Term, but currently the UPLC parser only attaches
-- a @SourcePos@ to each Term, while we'd need it to attach a @SrcSpan@.
mkUplcSpan
    :: PLC.SourcePos ->
    D.DTerm UPLC.DefaultUni UPLC.DefaultFun DAnn ->
    HighlightSpan
mkUplcSpan pos term = HighlightSpan sloc eloc
    where
        sline = unPos $ sourceLine pos
        scol = unPos $ sourceColumn pos
        sloc = B.Location (sline, scol)
        eloc = case delta of
            Nothing -> Nothing
            Just d ->
                let eline = sline
                    ecol = scol + d - 1
                 in Just $ B.Location (eline, ecol)
        delta = length <$> case term of
            UPLC.Var _ name -> Just . Text.unpack $ UPLC.ndbnString name
            UPLC.LamAbs{}   -> Just "lam"
            UPLC.Apply{}    -> Just "["
            UPLC.Force{}    -> Just "force"
            UPLC.Delay{}    -> Just "delay"
            UPLC.Constant{} -> Just "con"
            UPLC.Builtin{}  -> Just "builtin"
            UPLC.Error{}    -> Just "error"
