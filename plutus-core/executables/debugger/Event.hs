{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}

-- | Handler of debugger events.
module Event where

import PlutusCore.Annotation
import PlutusCore.Pretty qualified as PLC
import Types
import UntypedPlutusCore.Evaluation.Machine.SteppableCek.DebugDriver qualified as D
import UntypedPlutusCore.Evaluation.Machine.SteppableCek.Internal

import Brick.Focus qualified as B
import Brick.Main qualified as B
import Brick.Types qualified as B
import Brick.Widgets.Edit qualified as BE
import Control.Arrow ((>>>))
import Control.Concurrent.MVar
import Control.Monad.State
import Data.Coerce
import Data.Set as S
import Data.Text.Zipper
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
                B.zoom (dsSourceEditor.traversed) $ BE.handleEditorEvent bev
            Just EditorReturnValue ->
                B.zoom dsReturnValueEditor $ BE.handleEditorEvent bev
            Just EditorLogs ->
                B.zoom dsLogsEditor $ BE.handleEditorEvent bev
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
handleDebuggerEvent _ (B.AppEvent (UpdateClientEvent budgetData cekState)) = do
    let uplcHighlight :: Maybe HighlightSpan = do
            uplcSpan <- uplcAnn <$> cekStateAnn cekState
            pure HighlightSpan
                { _hcSLoc = B.Location (srcSpanSLine uplcSpan, srcSpanSCol uplcSpan),
                  -- The ending column of a `SrcSpan` is usually one more than the column of
                  -- the last character (same as GHC's `SrcSpan`), unless the last character
                  -- is the line break, hence the `- 1`.
                  _hcELoc = Just $ B.Location (srcSpanELine uplcSpan, srcSpanECol uplcSpan - 1)
                }
    let sourceHighlight :: Maybe HighlightSpan = do
            txSpans <- txAnn <$> cekStateAnn cekState
            -- FIXME: use some/all spans for highlighting, not just the first one
            firstTxSpan <- S.lookupMin $ coerce txSpans
            -- TODO: the HS_FILE supplied from the command line gets highlighted
            -- The highlighting will not make sense or even break if the user provides
            -- wrong HS_FILE or if the UPLC originated from multiple HS modules.
            pure HighlightSpan
                { _hcSLoc = B.Location (srcSpanSLine firstTxSpan, srcSpanSCol firstTxSpan),
                  -- GHC's SrcSpan's ending column is one larger than the last character's column.
                  -- See: ghc/compiler/GHC/Types/SrcLoc.hs#L728
                  _hcELoc = Just $ B.Location (srcSpanELine firstTxSpan, srcSpanECol firstTxSpan -1)
                }
    modify' $ \st ->
      st & set dsUplcHighlight uplcHighlight
         & set dsSourceHighlight sourceHighlight
         & set dsBudgetData budgetData
         & case cekState of
            Computing{} ->
               -- Clear the return value editor.
               dsReturnValueEditor .~
                BE.editorText
                    EditorReturnValue
                    Nothing
                    mempty
            Returning _ v ->
               dsReturnValueEditor .~
                BE.editorText
                    EditorReturnValue
                    Nothing
                    (PLC.displayPlcDef (dischargeCekValue v))
            Terminating t ->
               dsReturnValueEditor .~
                BE.editorText
                    EditorReturnValue
                    Nothing
                    (PLC.render $ vcat ["Evaluation Finished. Result:", line, PLC.prettyPlcDef t])
            Starting{} -> id
handleDebuggerEvent _ (B.AppEvent (ErrorEvent budgetData e)) =
    modify' $ \st ->
      -- Note that in case of an out-of-budget error (i.e. `CekOutOfExError`),
      -- the updated budgets (spent&remaining) here do not match the actual budgets
      -- on the chain: the difference is that on the chain, a budget may become zero (exhausted)
      -- but is not allowed to become negative.
      st & set dsBudgetData budgetData
         & dsLogsEditor %~ BE.applyEdit
           (gotoEOF >>>
            insertMany (PLC.render $ "Error happened:" <+> PLC.prettyPlcDef e) >>>
            breakLine
           )
handleDebuggerEvent _ _ = pure ()
