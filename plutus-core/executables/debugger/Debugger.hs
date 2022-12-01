{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}

-- | Logic for the debugging stage.
module Debugger where

import Common
import Types

import Brick.Focus qualified as B
import Brick.Types qualified as B
import Brick.Widgets.Border qualified as BB
import Brick.Widgets.Center qualified as BC
import Brick.Widgets.Core qualified as B
import Brick.Widgets.Edit qualified as BE
import Control.Monad.State
import Data.Bifunctor
import Data.Maybe
import Data.Text (Text)
import Data.Text qualified as Text
import Graphics.Vty qualified as Vty
import Lens.Micro

drawDebugger ::
    DebuggerState ->
    [B.Widget ResourceName]
drawDebugger st = [header "Plutus Core Debugger" $ BC.center ui]
  where
    focusRing = st ^. dsFocusRing
    (curRow, curCol) = BE.getCursorPosition (st ^. dsUplcEditor)
    cursorPos = "Ln " <> show (curRow + 1) <> ", Col " <> show (curCol + 1)
    uplcEditor =
        BB.borderWithLabel (B.txt "UPLC program") $
            B.vBox
                [ B.withFocusRing
                    focusRing
                    (BE.renderEditor drawTexts)
                    (st ^. dsUplcEditor)
                , B.padTop (B.Pad 1) . BC.hCenter $ B.str cursorPos
                ]
    sourceEditor =
        BB.borderWithLabel (B.txt "Source program") $
            B.withFocusRing
                focusRing
                (BE.renderEditor (B.txt . Text.unlines))
                (st ^. dsSourceEditor)
    returnValueEditor =
        BB.borderWithLabel (B.txt "UPLC value being returned") $
            B.withFocusRing
                focusRing
                (BE.renderEditor (B.txt . Text.unlines))
                (st ^. dsReturnValueEditor)
    cekStateEditor =
        BB.borderWithLabel (B.txt "CEK machine state") $
            B.withFocusRing
                focusRing
                (BE.renderEditor (B.txt . Text.unlines))
                (st ^. dsCekStateEditor)
    ui =
        B.vBox
            [ BC.center uplcEditor B.<+> BC.center sourceEditor
            , B.vLimit (st ^. dsVLimitBottomEditors) $
                BC.center returnValueEditor B.<+> BC.center cekStateEditor
            , footer
            ]
    drawTexts :: [Text] -> B.Widget ResourceName
    drawTexts =
        B.vBox
            . toWidgets
            -- This is needed for empty lines to be rendered correctly.
            -- `Brick.Widgets.Core.txt` does the same via `fixEmpty`.
            . fmap (\t -> if Text.null t then " " else t)

    toWidgets :: [Text] -> [B.Widget ResourceName]
    toWidgets rows = case st ^. dsUplcHighlight of
        Nothing -> B.txt <$> rows
        Just (HighlightCode (B.Location (sRow, sCol)) eLoc) ->
            let alg :: (Text, Int) -> B.Widget ResourceName
                alg (row, rowNo)
                    | rowNo < sRow || rowNo > eRow = B.txt row
                    -- The current line (either entirely or part of it) needs to be highlighted.
                    | otherwise =
                        let s =
                                if rowNo > sRow
                                    then 0
                                    else sCol - 1
                            e =
                                if rowNo < eRow
                                    then Text.length row
                                    else eCol
                            -- left -> no highlight
                            -- middle -> highlight
                            -- right -> no highlight
                            ((left, middle), right) = first (Text.splitAt s) (Text.splitAt e row)
                         in B.hBox $
                                [B.txt left | not (Text.null left)]
                                    ++ [ B.withAttr highlightAttr $ B.txt middle
                                       | not (Text.null middle)
                                       ]
                                    ++ [B.txt right | not (Text.null right)]
                  where
                    B.Location (eRow, eCol) = fromMaybe (B.Location (sRow, Text.length row)) eLoc
             in fmap alg (zip rows [1 ..])

-- | Handle events in the debugging stage
handleDebuggerEvent :: B.BrickEvent ResourceName e -> B.EventM ResourceName DebuggerState ()
handleDebuggerEvent bev@(B.VtyEvent ev) = do
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
    case ev of
        Vty.EvKey (Vty.KChar 's') [] -> modify' $ \st' ->
            -- Stepping. Currently it highlights one line at a time.
            let highlightNextLine = \case
                    Nothing ->
                        Just (HighlightCode (B.Location (1, 1)) Nothing)
                    Just (HighlightCode (B.Location (r, c)) _) ->
                        Just (HighlightCode (B.Location (r + 1, c)) Nothing)
             in st' & dsUplcHighlight %~ highlightNextLine
        Vty.EvKey (Vty.KChar '\t') [] -> modify' $ \st' ->
            st' & dsFocusRing %~ B.focusNext
        Vty.EvKey Vty.KBackTab [] -> modify' $ \st' ->
            st' & dsFocusRing %~ B.focusPrev
        Vty.EvKey Vty.KUp [Vty.MCtrl] -> modify' $ \st' ->
            st' & dsVLimitBottomEditors %~ (+ 1)
        Vty.EvKey Vty.KDown [Vty.MCtrl] -> modify' $ \st' ->
            st' & dsVLimitBottomEditors %~ (\x -> x - 1)
        Vty.EvKey Vty.KUp [] -> handleEditorEvent
        Vty.EvKey Vty.KDown [] -> handleEditorEvent
        Vty.EvKey Vty.KLeft [] -> handleEditorEvent
        Vty.EvKey Vty.KRight [] -> handleEditorEvent
        Vty.EvKey (Vty.KChar _) [] ->
            -- This disables editing the text, making the editors read-only.
            pure ()
        _ -> handleEditorEvent
handleDebuggerEvent _ = pure ()

debuggerKeyBindings :: forall n. B.Widget n
debuggerKeyBindings =
    B.vBox
        [ B.withAttr menuAttr . B.vBox $
            [ B.txt "Step            (s)"
            , B.txt "Move cursor     (Arrow)"
            , B.txt "Switch window   (Tab)"
            , B.txt "Resize windows  (^Up/^Down)"
            , B.txt "Quit            (Esc)"
            ]
        , B.txt "Press any key to exit"
        ]
