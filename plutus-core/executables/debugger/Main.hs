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

import PlutusCore qualified as PLC
import PlutusCore.Error
import PlutusCore.Evaluation.Machine.ExBudgetingDefaults qualified as PLC
import PlutusCore.Evaluation.Machine.MachineParameters
import PlutusCore.Executable.Common
import PlutusCore.Executable.Parsers
import PlutusCore.Pretty qualified as PLC
import UntypedPlutusCore as UPLC
import UntypedPlutusCore.Evaluation.Machine.Cek.Debug.Driver qualified as D
import UntypedPlutusCore.Evaluation.Machine.Cek.Debug.Internal
import UntypedPlutusCore.Parser qualified as UPLC

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
import Control.Monad.ST (RealWorld)
import Data.Text (Text)
import Data.Text.IO qualified as Text
import Graphics.Vty qualified as Vty
import Lens.Micro
import Options.Applicative qualified as OA
import UntypedPlutusCore.Core.Zip

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

data Options = Options
    { optUplcInput       :: Input
    , optUplcInputFormat :: Format
    -- MAYBE: make tx file optional? the SourceEditor should be hidden in that case then
    , optHsPath          :: FilePath
    }

parseOptions :: OA.Parser Options
parseOptions = do
    optUplcInput <- input
    optUplcInputFormat <- inputformat
    optHsPath <-
        OA.argument OA.str $
            mconcat
                [ OA.metavar "HS_FILE"
                , OA.help "HS File"
                ]
    pure Options{..}

main :: IO ()
main = do
    Options{..} <-
        OA.execParser $
            OA.info
                (parseOptions OA.<**> OA.helper)
                (OA.fullDesc <> OA.header "Plutus Core Debugger")

    (uplcText, uplcDAnn) <- getProgramWithText optUplcInputFormat optUplcInput

    hsText <- Text.readFile optHsPath

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
                        hsText
                , _dsSourceHighlight = Nothing
                , _dsReturnValueEditor =
                    BE.editorText
                        EditorReturnValue
                        Nothing
                        ""
                , _dsCekStateEditor =
                    BE.editorText
                        EditorCekState
                        Nothing
                        "What to show here is TBD"
                , _dsVLimitBottomEditors = 20
                , _dsHLimitRightEditors = 100
                }

    let builder = Vty.mkVty Vty.defaultConfig
    initialVty <- builder

    -- TODO: find out if the driver-thread exits when brick exits
    -- or should we wait for driver-thread?
    _dTid <- forkIO $ driverThread driverMailbox brickMailbox uplcDAnn

    void $ B.customMain initialVty builder (Just brickMailbox) app initialState

{- | The main entrypoint of the driver thread.

 The driver operates in IO (not in BrickM): the only way to "influence" Brick is via the mailboxes
-}
driverThread ::
    MVar (D.Cmd Breakpoints) ->
    B.BChan CustomBrickEvent ->
    Program Name DefaultUni DefaultFun DAnn ->
    IO ()
driverThread driverMailbox brickMailbox prog = do
    let term = prog ^. UPLC.progTerm
        MachineParameters cekcosts cekruntime = PLC.defaultCekParameters
    ndterm <- case runExcept @FreeVariableError $ deBruijnTerm term of
        Right t -> pure t
        Left _  -> fail $ "deBruijnTerm failed: " <> PLC.displayPlcDef (void term)
    let ?cekRuntime = cekruntime
        ?cekEmitter = const $ pure ()
        ?cekBudgetSpender = CekBudgetSpender $ \_ _ -> pure ()
        ?cekCosts = cekcosts
        ?cekSlippage = defaultSlippage
     in D.iterM handle $ D.runDriver ndterm
  where
    -- \| Peels off one Free monad layer
    handle ::
        GivenCekReqs DefaultUni DefaultFun DAnn RealWorld =>
        D.DebugF DefaultUni DefaultFun DAnn Breakpoints (IO a) ->
        IO a
    handle = \case
        D.StepF prevState k  -> cekMToIO (D.handleStep prevState) >>= k
        D.InputF k           -> handleInput >>= k
        D.LogF text k        -> handleLog text >> k
        D.UpdateClientF ds k -> handleUpdate ds >> k
      where
        handleInput = takeMVar driverMailbox
        handleUpdate = B.writeBChan brickMailbox . UpdateClientEvent
        handleLog = B.writeBChan brickMailbox . LogEvent

-- | Read uplc code in a given format
--
--  Adapted from `Common.getProgram`
getProgramWithText :: Format -> Input -> IO (Text, UplcProg DAnn)
getProgramWithText fmt inp =
    case fmt of
        Textual -> do
            -- here we use the original raw uplc text, we do not attempt any prettyfying
            (progTextRaw, progWithUplcSpan) <- parseInput inp
            let -- IMPORTANT: we cannot have any Tx.SourceSpans available in Textual mode
                -- We still show the SourceEditor but TX highlighting (or breakpointing) won't work.
                -- TODO: disable setting TX.breakpoints from inside the brick gui interface
                addEmptyTxSpans = fmap (`DAnn` mempty)
                progWithDAnn = addEmptyTxSpans progWithUplcSpan
            pure (progTextRaw, progWithDAnn)

        Flat flatMode -> do
            -- here comes the dance of flat-parsing->PRETTYfying->text-parsing
            -- so we can have artificial SourceSpans in annotations
            progWithTxSpans <- loadASTfromFlat @UplcProg @PLC.SrcSpans flatMode inp
            -- annotations are not pprinted by default, no need to `void`
            let progTextPretty = PLC.displayPlcDef progWithTxSpans

            -- the parsed prog with uplc.srcspan
            progWithUplcSpan <- either (fail . show @ParserErrorBundle) pure $ runExcept $
                                   PLC.runQuoteT $ UPLC.parseProgram progTextPretty

            -- zip back the two programs into one program with their annotations' combined
            -- the zip may fail if the AST cannot parse-pretty roundtrip (should not happen).
            progWithDAnn <- either fail pure $ runExcept $
                               pzipWith DAnn progWithUplcSpan progWithTxSpans

            pure (progTextPretty, progWithDAnn)
