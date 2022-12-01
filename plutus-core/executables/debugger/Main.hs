{-# LANGUAGE ApplicativeDo     #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards   #-}
{-# LANGUAGE StrictData        #-}
{-# LANGUAGE TypeApplications  #-}
{-# LANGUAGE ViewPatterns      #-}

{- | A Plutus Core debugger TUI application.

 The application has two stages: browsing for files to debug, and debugging.
 If the argument is a directory, it enters the browsing stage.
 If the argument is a file, it enters the debugging stage.
 If no argument is provided, it defaults to the current working directory.
-}
module Main (main) where

import Common
import Debugger
import FileBrowser
import Types

import Brick.AttrMap qualified as B
import Brick.Focus qualified as B
import Brick.Main qualified as B
import Brick.Types qualified as B
import Brick.Util qualified as B
import Brick.Widgets.Border qualified as BB
import Brick.Widgets.Center qualified as BC
import Brick.Widgets.Core qualified as B
import Brick.Widgets.Edit qualified as BE
import Brick.Widgets.FileBrowser qualified as BF
import Brick.Widgets.List qualified as BL
import Control.Applicative
import Control.Monad.Extra
import Control.Monad.State
import Data.Text.IO qualified as Text
import Graphics.Vty qualified as Vty
import Lens.Micro
import Options.Applicative qualified as OA
import System.Directory.Extra

-- | Render things in the terminal based on `DebuggerState`.
debuggerAppDraw :: DebuggerState -> [B.Widget ResourceName]
debuggerAppDraw st = withKeyBindingsOverlay
    (st ^. dsAppStage)
    (st ^. dsKeyBindingsMode)
    $ case st ^. dsAppStage of
        FileBrowsing -> drawFileBrowser (st ^. dsFileBrowser)
        Debugging    -> drawDebugger st

-- | Handle events when browsing files or debugging.
handleEvent ::
    B.BrickEvent ResourceName e ->
    B.EventM ResourceName DebuggerState ()
handleEvent bev = case bev of
    B.VtyEvent ev -> do
        st <- get
        case ev of
            Vty.EvKey{}
                | KeyBindingsShown <- st ^. dsKeyBindingsMode ->
                    modify' $ set dsKeyBindingsMode KeyBindingsHidden
            Vty.EvKey (Vty.KChar '?') [] ->
                modify' $ set dsKeyBindingsMode KeyBindingsShown
            Vty.EvKey Vty.KEsc []
                | not (BF.fileBrowserIsSearching (st ^. dsFileBrowser)) ->
                    B.halt
            _ -> case st ^. dsAppStage of
                FileBrowsing -> handleFileBrowserEvent ev
                Debugging    -> handleDebuggerEvent bev
    _ -> pure ()

-- | Show key bindings upon request.
withKeyBindingsOverlay ::
    AppStage ->
    KeyBindingsMode ->
    [B.Widget ResourceName] ->
    [B.Widget ResourceName]
withKeyBindingsOverlay stage = \case
    KeyBindingsShown  -> (BC.centerLayer (keyBindingsWindow stage) :)
    KeyBindingsHidden -> id

keyBindingsWindow :: forall n. AppStage -> B.Widget n
keyBindingsWindow stage = BB.borderWithLabel (B.txt "Key Bindings") $ case stage of
    FileBrowsing -> fileBrowserKeyBindings
    Debugging    -> debuggerKeyBindings

debuggerAttrMap :: DebuggerState -> B.AttrMap
debuggerAttrMap _ =
    B.attrMap
        Vty.defAttr
        [ (BL.listSelectedFocusedAttr, Vty.black `B.on` Vty.yellow)
        , (BF.fileBrowserCurrentDirectoryAttr, Vty.white `B.on` Vty.blue)
        , (BF.fileBrowserSelectionInfoAttr, Vty.white `B.on` Vty.blue)
        , (BF.fileBrowserDirectoryAttr, B.fg Vty.blue)
        , (BF.fileBrowserBlockDeviceAttr, B.fg Vty.magenta)
        , (BF.fileBrowserCharacterDeviceAttr, B.fg Vty.green)
        , (BF.fileBrowserNamedPipeAttr, B.fg Vty.yellow)
        , (BF.fileBrowserSymbolicLinkAttr, B.fg Vty.cyan)
        , (BF.fileBrowserUnixSocketAttr, B.fg Vty.red)
        , (BF.fileBrowserSelectedAttr, Vty.white `B.on` Vty.magenta)
        , (BE.editAttr, Vty.white `B.on` Vty.rgbColor @Int 32 32 32)
        , (BE.editFocusedAttr, Vty.white `B.on` Vty.black)
        , (menuAttr, Vty.withStyle (Vty.white `B.on` darkGreen) Vty.bold)
        , (highlightAttr, Vty.blue `B.on` Vty.white)
        ]

darkGreen :: Vty.Color
darkGreen = Vty.rgbColor @Int 0 100 0

newtype Options = Options
    {optPath :: Maybe FilePath}

parseOptions :: OA.Parser Options
parseOptions = do
    optPath <-
        -- Defaults to the current working directory.
        optional $
            OA.argument OA.str $
                mconcat
                    [ OA.metavar "UPLC_FILE_OR_DIR"
                    , OA.help "UPLC File or Dir (default: .)"
                    ]
    pure Options{..}

main :: IO ()
main = do
    opts <-
        OA.execParser $
            OA.info
                (parseOptions OA.<**> OA.helper)
                (OA.fullDesc <> OA.header "Plutus Core Debugger")
    whenJust (optPath opts) $ \path ->
        unlessM (doesPathExist path) . fail $ "Does not exist: " <> path
    fb <- BF.newFileBrowser BF.selectNonDirectories FileBrowserUplc (optPath opts)

    let app :: B.App DebuggerState e ResourceName
        app =
            B.App
                { B.appDraw = debuggerAppDraw
                , B.appChooseCursor = B.showFirstCursor
                , B.appHandleEvent = handleEvent
                , B.appStartEvent = pure ()
                , B.appAttrMap = debuggerAttrMap
                }
        initialState0 =
            DebuggerState
                { _dsAppStage = FileBrowsing
                , _dsFileBrowser = fb
                , _dsKeyBindingsMode = KeyBindingsHidden
                , _dsFocusRing =
                    B.focusRing
                        [ EditorUplc
                        , EditorSource
                        , EditorReturnValue
                        , EditorCekState
                        ]
                , _dsUplcEditor = BE.editorText EditorUplc Nothing mempty
                , _dsUplcHighlight = Nothing
                , _dsSourceEditor =
                    BE.editorText
                        EditorSource
                        Nothing
                        "Source code will be shown here"
                , _dsReturnValueEditor =
                    BE.editorText
                        EditorReturnValue
                        Nothing
                        "The value being returned will be shown here"
                , _dsCekStateEditor =
                    BE.editorText
                        EditorCekState
                        Nothing
                        "The CEK machine state will be shown here"
                , _dsVLimitBottomEditors = 20
                }
    initialState <- case optPath opts of
        Just path -> do
            isFile <- doesFileExist path
            if isFile
                then do
                    -- If the path argument is a file, enter Debugging stage directly
                    uplcText <- Text.readFile path
                    pure $
                        initialState0
                            & dsAppStage .~ Debugging
                            & dsUplcEditor .~ BE.editorText EditorUplc Nothing uplcText
                else pure initialState0
        _ -> pure initialState0
    void $ B.defaultMain app initialState
