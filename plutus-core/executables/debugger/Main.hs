{-# LANGUAGE ApplicativeDo     #-}
{-# LANGUAGE ImplicitParams    #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards   #-}
{-# LANGUAGE StrictData        #-}
{-# LANGUAGE TupleSections     #-}
{-# LANGUAGE TypeApplications  #-}

{- | A Plutus Core debugger TUI application.

 The application has two stages: browsing for files to debug, and debugging.
 If the argument is a directory, it enters the browsing stage.
 If the argument is a file, it enters the debugging stage.
 If no argument is provided, it defaults to the current working directory.
-}
module Main (main) where

import Annotation
import PlutusCore qualified as PLC
import PlutusCore.Error
import PlutusCore.Evaluation.Machine.ExBudgetingDefaults qualified as PLC
import PlutusCore.Evaluation.Machine.MachineParameters
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
import Control.Monad.Extra
import Control.Monad.ST (RealWorld)
import Data.ByteString.Lazy qualified as Lazy
import Data.Text (Text)
import Data.Text qualified as Text
import Data.Text.IO qualified as Text
import Flat
import Graphics.Vty qualified as Vty
import Lens.Micro
import Options.Applicative qualified as OA
import System.Directory.Extra
import Text.Megaparsec (unPos)

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
    {optUplcPath :: FilePath, optHsPath :: FilePath}

parseOptions :: OA.Parser Options
parseOptions = do
    optUplcPath <-
        OA.argument OA.str $
            mconcat
                [ OA.metavar "UPLC_FILE"
                , OA.help "UPLC File"
                ]
    optHsPath <-
        OA.argument OA.str $
            mconcat
                [ OA.metavar "HS_FILE"
                , OA.help "HS File"
                ]
    pure Options{..}

main :: IO ()
main = do
    opts <-
        OA.execParser $
            OA.info
                (parseOptions OA.<**> OA.helper)
                (OA.fullDesc <> OA.header "Plutus Core Debugger")

    unlessM (doesFileExist (optUplcPath opts)) . fail $
        "Does not exist or not a file: " <> optUplcPath opts
    uplcFlat <- Lazy.readFile (optUplcPath opts)
    uplcDebruijn <-
        either
            (\e -> fail $ "UPLC deserialisation failure:" <> show e)
            pure
            (unflat uplcFlat)
    uplcNoAnn <- unDeBruijnProgram uplcDebruijn
    let uplcText = PLC.displayPlcDef uplcNoAnn
    uplcParsed <-
        either (error . show @ParserErrorBundle) pure . PLC.runQuoteT $
            UPLC.parseProgram uplcText
    let uplc =
            fmap
                ( \(pos, token) ->
                    let sp =
                            SrcSpan
                                { srcSpanFile = sourceName pos
                                , srcSpanSLine = unPos (sourceLine pos)
                                , srcSpanSCol = unPos (sourceColumn pos)
                                , srcSpanELine = unPos (sourceLine pos)
                                , srcSpanECol = unPos (sourceColumn pos) + Text.length token - 1
                                }
                     in DAnn sp mempty
                )
                $ zipProgramWithFirstToken uplcParsed

    hsText <- Text.readFile (optHsPath opts)

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
    _dTid <- forkIO $ driverThread driverMailbox brickMailbox uplc

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
        D.UpdateClientF ds k -> handleUpdate ds >> k -- TODO: implement
      where
        handleInput = takeMVar driverMailbox
        handleUpdate = B.writeBChan brickMailbox . UpdateClientEvent
        handleLog = B.writeBChan brickMailbox . LogEvent

unDeBruijnProgram ::
    UPLC.Program UPLC.NamedDeBruijn DefaultUni DefaultFun () ->
    IO (UPLC.Program UPLC.Name DefaultUni DefaultFun ())
unDeBruijnProgram p = do
    either (fail . show) pure
        . PLC.runQuote
        . runExceptT @UPLC.FreeVariableError
        $ traverseOf UPLC.progTerm UPLC.unDeBruijnTerm p

zipProgramWithFirstToken ::
    Program Name uni fun ann ->
    Program Name uni fun (ann, Text)
zipProgramWithFirstToken (Program ann ver t) =
    Program (ann, "program") (fmap (,"program") ver) (zipTermWithFirstToken t)

{- | Attempt to highlight the first token of a `Term`, by annotating the `Term` with
 the first token of the pretty-printed `Term`. This is a temporary workaround.

 Ideally we want to highlight the entire `Term`, but currently the UPLC parser only attaches
 a `SourcePos` to each `Term`, while we'd need it to attach a `SrcSpan`.
-}
zipTermWithFirstToken :: Term Name uni fun ann -> Term Name uni fun (ann, Text)
zipTermWithFirstToken = go
  where
    go = \case
        Var ann name         -> Var (ann, UPLC._nameText name) name
        LamAbs ann name body -> LamAbs (ann, "lam") name (go body)
        Apply ann fun arg    -> Apply (ann, "[") (go fun) (go arg)
        Force ann body       -> Force (ann, "force") (go body)
        Delay ann body       -> Delay (ann, "delay") (go body)
        Constant ann val     -> Constant (ann, "con") val
        Builtin ann fun      -> Builtin (ann, "builtin") fun
        Error ann            -> Error (ann, "error")
