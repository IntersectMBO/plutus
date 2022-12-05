{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}

-- | Renders the debugger in the terminal.
module Draw where

import Types

import Brick.AttrMap qualified as B
import Brick.Focus qualified as B
import Brick.Types qualified as B
import Brick.Widgets.Border qualified as BB
import Brick.Widgets.Center qualified as BC
import Brick.Widgets.Core qualified as B
import Brick.Widgets.Edit qualified as BE
import Data.Bifunctor
import Data.Maybe
import Data.Text (Text)
import Data.Text qualified as Text
import Lens.Micro

drawDebugger ::
    DebuggerState ->
    [B.Widget ResourceName]
drawDebugger st =
    withKeyBindingsOverlay
        (st ^. dsKeyBindingsMode)
        [header "Plutus Core Debugger" $ BC.center ui]
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

-- | Show key bindings upon request.
withKeyBindingsOverlay ::
    KeyBindingsMode ->
    [B.Widget ResourceName] ->
    [B.Widget ResourceName]
withKeyBindingsOverlay = \case
    KeyBindingsShown  -> (BC.centerLayer debuggerKeyBindings :)
    KeyBindingsHidden -> id

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

menuAttr :: B.AttrName
menuAttr = B.attrName "menu"

highlightAttr :: B.AttrName
highlightAttr = B.attrName "highlight"

header :: Text -> B.Widget a -> B.Widget a
header title =
    (B.vLimit 1 (B.withAttr menuAttr . BC.hCenter $ B.txt title) B.<=>)

footer :: forall a. B.Widget a
footer =
    B.padTop (B.Pad 1) . BC.hCenter . B.withAttr menuAttr $
        B.txt "(?): Key Bindings"
