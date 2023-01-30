{-# LANGUAGE ApplicativeDo     #-}
{-# LANGUAGE ImplicitParams    #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards   #-}
{-# LANGUAGE StrictData        #-}
{-# LANGUAGE TypeApplications  #-}

{- | A Plutus Core debugger TUI application.

 The application has two stages: browsing for files to debug, and debugging.
 If the argument is a directory, it enters the browsing stage.
 If the argument is a file, it enters the debugging stage.
 If no argument is provided, it defaults to the current working directory.
-}
module Main (main) where

import PlutusCore.Evaluation.Machine.ExBudgetingDefaults qualified as PLC
import PlutusCore.Evaluation.Machine.MachineParameters
import UntypedPlutusCore as UPLC
import UntypedPlutusCore.Evaluation.Machine.Cek.Debug.Driver qualified as D
import UntypedPlutusCore.Evaluation.Machine.Cek.Debug.Internal

import Draw
import Event
import Types

import Brick.AttrMap qualified as B
import Brick.BChan qualified as B
import Brick.Focus qualified as B
import Brick.Main qualified as B
import Brick.Util qualified as B
import Brick.Widgets.Edit qualified as BE
import Control.Concurrent
import Control.Monad.Except
import Control.Monad.Extra
import Control.Monad.ST (RealWorld)
import Data.Text qualified as Text
import Data.Text.IO qualified as Text
import Graphics.Vty qualified as Vty
import Options.Applicative qualified as OA
import PlutusPrelude
import System.Directory.Extra

debuggerAttrMap :: B.AttrMap
debuggerAttrMap =
    B.attrMap
        Vty.defAttr
        [ (BE.editAttr, Vty.white `B.on` Vty.rgbColor @Int 32 32 32)
        , (BE.editFocusedAttr, Vty.white `B.on` Vty.black)
        , (menuAttr, Vty.withStyle (Vty.white `B.on` darkGreen) Vty.bold)
        , (highlightAttr, Vty.blue `B.on` Vty.white)
        ]

darkGreen :: Vty.Color
darkGreen = Vty.rgbColor @Int 0 100 0

newtype Options = Options
    {optPath :: FilePath}

parseOptions :: OA.Parser Options
parseOptions = do
    optPath <-
        OA.argument OA.str $
            mconcat
                [ OA.metavar "UPLC_FILE"
                , OA.help "UPLC File"
                ]
    pure Options{..}

main :: IO ()
main = do
    opts <-
        OA.execParser $
            OA.info
                (parseOptions OA.<**> OA.helper)
                (OA.fullDesc <> OA.header "Plutus Core Debugger")

    unlessM (doesFileExist (optPath opts)) . fail $
        "Does not exist or not a file: " <> optPath opts
    uplcText <- Text.readFile (optPath opts)

    -- The communication "channels" at debugger-driver and at brick
    driverMailbox <- newEmptyMVar @(D.Cmd Breakpoints)
    -- chan size of 20 is used as default for builtin non-custom events (mouse,key,etc)
    brickMailbox <- B.newBChan @CustomBrickEvent 20

    let app :: B.App DebuggerState CustomBrickEvent ResourceName
        app =
            B.App
                { B.appDraw = drawDebugger
                , B.appChooseCursor = B.showFirstCursor
                , B.appHandleEvent = handleDebuggerEvent driverMailbox
                , B.appStartEvent = pure ()
                , B.appAttrMap = const debuggerAttrMap
                }
        initialState =
            DebuggerState
                { _dsKeyBindingsMode = KeyBindingsHidden
                , _dsFocusRing =
                    B.focusRing
                        [ EditorUplc
                        , EditorSource
                        , EditorReturnValue
                        , EditorCekState
                        ]
                , _dsUplcEditor = BE.editorText EditorUplc Nothing uplcText
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

    let builder = Vty.mkVty Vty.defaultConfig
    initialVty <- builder

    -- TODO: find out if the driver-thread exits when brick exits
    -- or should we wait for driver-thread?
    _dTid <- forkIO $ driverThread driverMailbox brickMailbox uplcText

    void $ B.customMain initialVty builder (Just brickMailbox) app initialState

-- | The custom events that can arrive at our brick mailbox.
data CustomBrickEvent =
    UpdateClientEvent (D.CekState DefaultUni DefaultFun DAnn)
    -- ^ the driver passes a new cek state to the brick client
    -- this should mean that the brick client should update its tui
  | LogEvent String
    -- ^ the driver logged some text, the brick client can decide to show it in the tui


-- | The main entrypoint of the driver thread.
--
-- The driver operates in IO (not in BrickM): the only way to "influence" Brick is via the mailboxes
driverThread :: MVar (D.Cmd Breakpoints) -> B.BChan CustomBrickEvent -> Text.Text -> IO ()
driverThread driverMailbox brickMailbox _uplcText = do
    let term = undefined -- void $ prog ^. UPLC.progTerm
        MachineParameters cekcosts cekruntime = PLC.defaultCekParameters
    let ndterm = fromRight undefined $ runExcept @FreeVariableError $ deBruijnTerm term
        emptySrcSpansNdDterm = fmap (undefined) ndterm
    let ?cekRuntime = cekruntime
        ?cekEmitter = const $ pure ()
        ?cekBudgetSpender = CekBudgetSpender $ \_ _ -> pure ()
        ?cekCosts = cekcosts
        ?cekSlippage = defaultSlippage
      in D.iterM handle $ D.runDriver emptySrcSpansNdDterm
  where
    -- | Peels off one Free monad layer
    handle :: GivenCekReqs DefaultUni DefaultFun DAnn RealWorld
           => D.DebugF DefaultUni DefaultFun DAnn Breakpoints (IO a)
           -> IO a
    handle = \case
        D.StepF prevState k  -> cekMToIO (D.handleStep prevState) >>= k
        D.InputF k           -> handleInput >>= k
        D.LogF text k        -> handleLog text >> k
        D.UpdateClientF ds k -> handleUpdate ds >> k -- TODO: implement
      where
        handleInput = takeMVar driverMailbox
        handleUpdate = B.writeBChan brickMailbox . UpdateClientEvent
        handleLog = B.writeBChan brickMailbox . LogEvent
