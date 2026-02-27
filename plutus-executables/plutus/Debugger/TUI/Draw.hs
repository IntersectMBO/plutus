{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

-- | Renders the debugger in the terminal.
module Debugger.TUI.Draw where

import Debugger.TUI.Types
import PlutusPrelude (render)

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
import Prettyprinter hiding (line)

drawDebugger
  :: DebuggerState
  -> [B.Widget ResourceName]
drawDebugger st =
  withKeyBindingsOverlay
    (st ^. dsKeyBindingsMode)
    [header "Plutus Core Debugger" $ BC.center ui]
  where
    focusRing = st ^. dsFocusRing
    (curLine, curCol) = BE.getCursorPosition (st ^. dsUplcEditor)
    cursorPos = "Ln " <> show (curLine + 1) <> ", Col " <> show (curCol + 1)
    uplcEditor =
      BB.borderWithLabel (B.txt "UPLC program") $
        B.vBox
          [ B.withFocusRing
              focusRing
              (BE.renderEditor (drawDocumentWithHighlight (st ^. dsUplcHighlight)))
              (st ^. dsUplcEditor)
          , B.padTop (B.Pad 1) . BC.hCenter $ B.str cursorPos
          ]
    sourceEditor =
      maybe
        B.emptyWidget
        ( BB.borderWithLabel (B.txt "Source program")
            . B.withFocusRing
              focusRing
              (BE.renderEditor (drawDocumentWithHighlight (st ^. dsSourceHighlight)))
        )
        (st ^. dsSourceEditor)
    returnValueEditor =
      BB.borderWithLabel (B.txt "UPLC value being returned") $
        B.withFocusRing
          focusRing
          (BE.renderEditor (B.txt . Text.unlines))
          (st ^. dsReturnValueEditor)
    logsEditor =
      BB.borderWithLabel (B.txt "Logs") $
        B.withFocusRing
          focusRing
          (BE.renderEditor (B.txt . Text.unlines))
          (st ^. dsLogsEditor)
    budgetTxt =
      B.hBox
        [ prettyTxt "Spent:" (st ^. dsBudgetData . budgetSpent)
        , -- do not show Remaining in absence of `--budget`
          maybe B.emptyWidget (prettyTxt "Remaining:") (st ^. dsBudgetData . budgetRemaining)
        ]
    prettyTxt title = B.txt . render . group . (title <>) . pretty

    ui =
      B.vBox
        [ BC.center uplcEditor B.<+> B.hLimit (st ^. dsHLimitRightEditors) sourceEditor
        , B.vLimit (st ^. dsVLimitBottomEditors) $
            BC.center returnValueEditor
              B.<+> B.hLimit (st ^. dsHLimitRightEditors) logsEditor
        , budgetTxt
        , footer
        ]

-- | Draw a document, a consecutive part of which may be highlighted.
drawDocumentWithHighlight
  :: forall n
   . Maybe HighlightSpan
  -- ^ The part of the document to be highlighted.
  -> [Text]
  -- ^ The document to draw, one `Text` per line.
  -> B.Widget n
drawDocumentWithHighlight = \case
  Nothing -> B.txt . Text.unlines
  Just (HighlightSpan (B.Location (sLine, sCol)) eLoc) ->
    let toWidgets :: [Text] -> [B.Widget n]
        toWidgets lns =
          let alg :: (Text, Int) -> B.Widget n
              alg (line, lineNo)
                | lineNo < sLine || lineNo > eLine = B.txt line
                -- The current line (either entirely or part of it) needs to be highlighted.
                | otherwise =
                    let s =
                          if lineNo > sLine
                            then 0
                            else sCol - 1
                        e =
                          if lineNo < eLine
                            then Text.length line
                            else eCol
                     in highlightLine line s e
                where
                  B.Location (eLine, eCol) =
                    fromMaybe
                      (B.Location (sLine, Text.length line))
                      eLoc
           in fmap alg (zip lns [1 ..])
     in B.vBox
          . toWidgets
          -- This is needed for empty lines to be rendered correctly.
          -- `Brick.Widgets.Core.txt` does the same via `fixEmpty`.
          . fmap (\t -> if Text.null t then " " else t)

-- | Draw a line and highlight from the start column to the end column.
highlightLine
  :: forall n
   . Text
  -> Int
  -- ^ Start column

  -- End column
  -> Int
  -> B.Widget n
highlightLine line s e =
  B.hBox $
    [B.txt left | not (Text.null left)]
      ++ [ B.withAttr highlightAttr $ B.txt middle
         | not (Text.null middle)
         ]
      ++ [B.txt right | not (Text.null right)]
  where
    -- left -> no highlight
    -- middle -> highlight
    -- right -> no highlight
    ((left, middle), right) = first (Text.splitAt s) (Text.splitAt e line)

-- | Show key bindings upon request.
withKeyBindingsOverlay
  :: KeyBindingsMode
  -> [B.Widget ResourceName]
  -> [B.Widget ResourceName]
withKeyBindingsOverlay = \case
  KeyBindingsShown -> (BC.centerLayer debuggerKeyBindings :)
  KeyBindingsHidden -> id

debuggerKeyBindings :: forall n. B.Widget n
debuggerKeyBindings =
  B.vBox
    [ B.withAttr menuAttr . B.vBox $
        [ B.txt "Step            (s)"
        , B.txt "Move cursor     (Arrow)"
        , B.txt "Switch window   (Tab)"
        , B.txt "Resize windows  (^Up/^Down/^Left/^Right)"
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
