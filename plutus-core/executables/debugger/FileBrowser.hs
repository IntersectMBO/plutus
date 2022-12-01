{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}

-- | Logic for the file browsing stage.
module FileBrowser where

import Common
import Types

import Brick.Types qualified as B
import Brick.Widgets.Border qualified as BB
import Brick.Widgets.Center qualified as BC
import Brick.Widgets.Core qualified as B
import Brick.Widgets.Edit qualified as BE
import Brick.Widgets.FileBrowser qualified as BF
import Control.Monad.State
import Data.Text.IO qualified as Text
import Graphics.Vty qualified as Vty
import Lens.Micro

drawFileBrowser ::
    BF.FileBrowser ResourceName -> [B.Widget ResourceName]
drawFileBrowser fb = [BC.center ui]
  where
    ui =
        BC.hCenter
            . B.vLimit 40
            . B.hLimit 120
            . BB.borderWithLabel (B.txt "Choose a UPLC program file")
            $ B.vBox [BF.renderFileBrowser True fb, footer]

-- | Handle events in the file browsing stage
handleFileBrowserEvent :: Vty.Event -> B.EventM ResourceName DebuggerState ()
handleFileBrowserEvent ev = do
    B.zoom dsFileBrowser $ BF.handleFileBrowserEvent ev
    case ev of
        Vty.EvKey Vty.KEnter [] -> do
            fb <- gets (^. dsFileBrowser)
            case BF.fileBrowserSelection fb of
                [] -> pure ()
                debuggee : _ -> do
                    -- A debuggee is selected. Entering the Debugging stage.
                    uplcText <-
                        liftIO $
                            Text.readFile (BF.fileInfoFilePath debuggee)
                    modify' $ \st' ->
                        st'
                            & dsAppStage .~ Debugging
                            & dsUplcEditor .~ BE.editorText EditorUplc Nothing uplcText
        _ -> pure ()
    pure ()

fileBrowserKeyBindings :: forall n. B.Widget n
fileBrowserKeyBindings =
    B.vBox
        [ B.withAttr menuAttr . B.vBox $
            [ B.txt "Move cursor                      (Up/Down)"
            , B.txt "Search                           (/)"
            , B.txt "Cancel Search                    (^c) or (ESC)"
            , B.txt "Change directory or select file  (Enter)"
            , B.txt "Quit                             (Esc)"
            ]
        , B.txt "Press any key to exit"
        ]
