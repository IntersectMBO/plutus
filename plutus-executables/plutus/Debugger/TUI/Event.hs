{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}

-- | Handler of debugger events.
module Debugger.TUI.Event where

import Data.Foldable (for_)
import Debugger.TUI.Types
import PlutusCore.Annotation
import PlutusCore.Pretty qualified as PLC
import UntypedPlutusCore.Evaluation.Machine.SteppableCek.DebugDriver qualified as D
import UntypedPlutusCore.Evaluation.Machine.SteppableCek.Internal

import Brick.Focus qualified as B
import Brick.Main qualified as B
import Brick.Types qualified as B
import Brick.Widgets.Edit qualified as BE

-- ghc>=9.6 has this in base
#if ! MIN_VERSION_base(4,18,0)
import Control.Applicative (liftA2)
#endif
import Control.Arrow ((>>>))
import Control.Concurrent.MVar
import Control.Monad.Catch
import Control.Monad.State
import Data.Coerce
import Data.Set as S
import Data.Text.IO qualified as Text
import Data.Text.Zipper
import Graphics.Vty qualified as Vty
import Lens.Micro
import Prettyprinter
import System.FilePath

handleDebuggerEvent
  :: MVar (D.Cmd Breakpoints)
  -> Maybe FilePath
  -> B.BrickEvent ResourceName CustomBrickEvent
  -> B.EventM ResourceName DebuggerState ()
handleDebuggerEvent driverMailbox _ bev@(B.VtyEvent ev) = do
  focusRing <- gets (^. dsFocusRing)
  let handleEditorEvent = case B.focusGetCurrent focusRing of
        Just EditorUplc ->
          B.zoom dsUplcEditor $ BE.handleEditorEvent bev
        Just EditorSource ->
          B.zoom (dsSourceEditor . traversed) $ BE.handleEditorEvent bev
        Just EditorReturnValue ->
          B.zoom dsReturnValueEditor $ BE.handleEditorEvent bev
        Just EditorLogs ->
          B.zoom dsLogsEditor $ BE.handleEditorEvent bev
        _ -> pure ()
  keyBindingsMode <- gets (^. dsKeyBindingsMode)
  case ev of
    Vty.EvKey {}
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
handleDebuggerEvent _ hsDir (B.AppEvent (UpdateClientEvent budgetData cekState)) = do
  let muplcHighlight :: Maybe HighlightSpan = do
        uplcSpan <- uplcAnn <$> cekStateAnn cekState
        pure
          HighlightSpan
            { _hcSLoc = B.Location (srcSpanSLine uplcSpan, srcSpanSCol uplcSpan)
            , -- The ending column of a `SrcSpan` is usually one more than the column of
              -- the last character (same as GHC's `SrcSpan`), unless the last character
              -- is the line break, hence the `- 1`.
              _hcELoc = Just $ B.Location (srcSpanELine uplcSpan, srcSpanECol uplcSpan - 1)
            }

  let msourceSrcSpan :: Maybe SrcSpan = do
        txSpans <- txAnn <$> cekStateAnn cekState
        -- FIXME: use some/all spans for highlighting, not just the first one
        -- because now we arbitrary selected the first (in-order) srcsspan
        firstTxSpan <- S.lookupMin $ coerce txSpans
        pure firstTxSpan

  let msourceHighlight :: Maybe HighlightSpan = do
        sourceSrcSpan <- msourceSrcSpan
        pure
          HighlightSpan
            { _hcSLoc =
                B.Location
                  ( srcSpanSLine sourceSrcSpan
                  , srcSpanSCol sourceSrcSpan
                  )
            , -- GHC's SrcSpan's ending column is one larger than the last character's column.
              -- See: ghc/compiler/GHC/Types/SrcLoc.hs#L728
              _hcELoc =
                Just $
                  B.Location
                    ( srcSpanELine sourceSrcSpan
                    , srcSpanECol sourceSrcSpan - 1
                    )
            }
  -- the current sourcespan may have jumped to another hs file, update the text of the editor
  for_ (liftA2 (</>) hsDir $ srcSpanFile <$> msourceSrcSpan) $ \file ->
    do
      res <- liftIO $ Text.readFile file
      -- putting modify directly in here has the upside (or downside) that
      -- it keeps the old tx shown in the tx panel when we the jumped tx-sourcespan is empty
      modify' $ \st ->
        st
          & dsSourceEditor
            .~ ( BE.editorText
                   EditorSource
                   Nothing
                   <$> Just res
               )
      `catchAll` \e ->
        modify' $ appendToLogsEditor ("DEBUGGER ERROR:" <+> viaShow e)

  modify' $ \st ->
    st
      & set dsUplcHighlight muplcHighlight
      & set dsSourceHighlight msourceHighlight
      & set dsBudgetData budgetData
      -- & dsSourceEditor .~
      --      (BE.editorText
      --          EditorSource
      --          Nothing <$> msourceText)
      & case cekState of
        Computing {} ->
          -- Clear the return value editor.
          dsReturnValueEditor
            .~ BE.editorText
              EditorReturnValue
              Nothing
              mempty
        Returning _ v ->
          dsReturnValueEditor
            .~ BE.editorText
              EditorReturnValue
              Nothing
              (PLC.displayPlc (dischargeCekValue v))
        Terminating t ->
          dsReturnValueEditor
            .~ BE.editorText
              EditorReturnValue
              Nothing
              (PLC.render $ vcat ["Evaluation Finished. Result:", line, PLC.prettyPlc t])
        Starting {} -> id
handleDebuggerEvent _ _ (B.AppEvent (CekErrorEvent budgetData e)) =
  modify' $ \st ->
    -- Note that in case of an out-of-budget error (i.e. `CekOutOfExError`),
    -- the updated budgets (spent&remaining) here do not match the actual budgets
    -- on the chain: the difference is that on the chain, a budget may become zero (exhausted)
    -- but is not allowed to become negative.
    st
      & set dsBudgetData budgetData
      & appendToLogsEditor ("Error happened:" <+> PLC.prettyPlc e)
handleDebuggerEvent _ _ (B.AppEvent (DriverLogEvent t)) =
  modify' $ appendToLogsEditor ("Driver logged:" <+> pretty t)
handleDebuggerEvent _ _ (B.AppEvent (CekEmitEvent t)) =
  modify' $ appendToLogsEditor ("CEK emitted:" <+> pretty t)
handleDebuggerEvent _ _ _ = pure ()

appendToLogsEditor :: Doc ann -> DebuggerState -> DebuggerState
appendToLogsEditor msg =
  dsLogsEditor
    %~ BE.applyEdit
      ( gotoEOF
          >>> insertMany (PLC.render msg)
          >>> breakLine
      )
