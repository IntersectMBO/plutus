{-# LANGUAGE ApplicativeDo       #-}
{-# LANGUAGE ImplicitParams      #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE NamedFieldPuns      #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StrictData          #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeFamilies        #-}

{- | A Plutus Core debugger TUI application.

 The application has two stages: browsing for files to debug, and debugging.
 If the argument is a directory, it enters the browsing stage.
 If the argument is a file, it enters the debugging stage.
 If no argument is provided, it defaults to the current working directory.
-}
module Main (main) where

import PlutusCore qualified as PLC
import PlutusCore.Error
import PlutusCore.Evaluation.Machine.ExBudget
import PlutusCore.Evaluation.Machine.ExBudgetingDefaults qualified as PLC
import PlutusCore.Executable.Common
import PlutusCore.Executable.Parsers
import PlutusCore.Pretty qualified as PLC
import UntypedPlutusCore as UPLC
import UntypedPlutusCore.Core.Zip
import UntypedPlutusCore.Evaluation.Machine.Cek
import UntypedPlutusCore.Evaluation.Machine.SteppableCek.DebugDriver qualified as D
import UntypedPlutusCore.Evaluation.Machine.SteppableCek.Internal
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
import Data.Coerce
import Data.Maybe
import Data.Text (Text)
import Data.Text.IO qualified as Text
import Data.Traversable
import GHC.IO (stToIO)
import Graphics.Vty qualified as Vty
import Lens.Micro
import Options.Applicative qualified as OA
import Text.Megaparsec as MP
import Text.Megaparsec.Char as MP
import Text.Megaparsec.Char.Lexer as MP

{- NOTE [Budgeting implementation for the debugger]
To retrieve the budget(s) (spent and remaining), we cannot simply
rely on `CekState`: the debuggable version of CEK tries to closely match the original CEK and
so it also inherits its pluggable spenders/emitters approach. Thus, for the debugger as well
we need to construct a budget mode (incl. a spender function) so we can have proper
budget accounting.

We could go with implementing a custom budget mode specifically for the
debugger (e.g. one that can talk directly to brick via events), but we opted instead to reuse
the `counting` and `restricting` modes, already built for the original cek.
-}

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
    , optHsPath          :: Maybe FilePath
    , optBudgetLim       :: Maybe ExBudget
    }

parseOptions :: OA.Parser Options
parseOptions = do
    optUplcInput <- input
    optUplcInputFormat <- inputformat
    optHsPath <- OA.optional $ OA.strOption $
                   mconcat
                      [ OA.metavar "HS_FILE"
                      , OA.long "hs-file"
                      , OA.help "HS File"
                      ]
    -- Having cpu mem as separate options complicates budget modes (counting vs restricting);
    -- instead opt for having both present (cpu,mem) or both missing.
    optBudgetLim <- OA.optional $ OA.option budgetReader $
                    mconcat
                      [ OA.metavar "INT,INT"
                      , OA.long "budget"
                      , OA.help "Limit the execution budget, given in terms of CPU,MEMORY"
                      ]
    pure Options{optUplcInput, optUplcInputFormat, optHsPath, optBudgetLim}
  where
      budgetReader = OA.maybeReader $ MP.parseMaybe @() budgetParser
      budgetParser = ExBudget <$> MP.decimal <* MP.char ',' <*> MP.decimal

main :: IO ()
main = do
    Options{optUplcInput, optUplcInputFormat, optHsPath, optBudgetLim} <-
        OA.execParser $
            OA.info
                (parseOptions OA.<**> OA.helper)
                (OA.fullDesc <> OA.header "Plutus Core Debugger")

    (uplcText, uplcDAnn) <- getProgramWithText optUplcInputFormat optUplcInput

    hsText <- traverse Text.readFile optHsPath

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
                    B.focusRing $ catMaybes
                        [ Just EditorUplc
                        , EditorSource <$ optHsPath
                        , Just EditorReturnValue
                        , Just EditorLogs
                        ]
                , _dsUplcEditor = BE.editorText EditorUplc Nothing uplcText
                , _dsUplcHighlight = Nothing
                , _dsSourceEditor =
                    BE.editorText
                        EditorSource
                        Nothing <$>
                        hsText
                , _dsSourceHighlight = Nothing
                , _dsReturnValueEditor =
                    BE.editorText
                        EditorReturnValue
                        Nothing
                        ""
                , _dsLogsEditor =
                    BE.editorText
                        EditorLogs
                        Nothing
                        ""
                , _dsVLimitBottomEditors = 20
                , _dsHLimitRightEditors = 100
                , _dsBudgetData = BudgetData
                    { _budgetSpent = mempty
                      -- the initial remaining budget is based on the passed cli arguments
                    , _budgetRemaining = optBudgetLim
                    }
                }

    let builder = Vty.mkVty Vty.defaultConfig
    initialVty <- builder

    -- TODO: find out if the driver-thread exits when brick exits
    -- or should we wait for driver-thread?
    _dTid <- forkIO $ driverThread driverMailbox brickMailbox uplcDAnn optBudgetLim

    void $ B.customMain initialVty builder (Just brickMailbox) app initialState

{- | The main entrypoint of the driver thread.

 The driver operates in IO (not in BrickM): the only way to "influence" Brick is via the mailboxes
-}
driverThread :: forall uni fun ann
             .  (uni ~ DefaultUni, fun ~ DefaultFun, ann ~ DAnn)
             => MVar (D.Cmd Breakpoints)
             -> B.BChan CustomBrickEvent
             -> Program Name uni fun ann
             -> Maybe ExBudget
             -> IO ()
driverThread driverMailbox brickMailbox prog mbudget = do
    let term = prog ^. UPLC.progTerm
    ndterm <- case runExcept @FreeVariableError $ deBruijnTerm term of
            Right t -> pure t
            Left _  -> fail $ "deBruijnTerm failed: " <> PLC.displayPlcDef (void term)
    -- if user provided `--budget` the mode is restricting; otherwise just counting
    -- See NOTE [Budgeting implementation for the debugger]
    let exBudgetMode = case mbudget of
            Just budgetLimit -> coerceMode $ restricting $ ExRestrictingBudget budgetLimit
            _                -> coerceMode counting
    -- TODO: implement emitter
    -- nilSlippage is important so as to get correct live up-to-date budget
    cekTransWithBudgetRead <- mkCekTrans PLC.defaultCekParameters exBudgetMode noEmitter nilSlippage
    D.iterM (handle cekTransWithBudgetRead) $ D.runDriverT ndterm

    where
        -- this gets rid of the CountingSt/RestrictingSt newtype wrappers
        -- See NOTE [Budgeting implementation for the debugger]
        coerceMode :: Coercible cost ExBudget
                   => ExBudgetMode cost uni fun
                   -> ExBudgetMode ExBudget uni fun
        coerceMode = coerce

        -- Peels off one Free monad layer
        -- Note to self: for some reason related to implicit params I cannot turn the following
        -- into a let block and avoid passing exbudgetinfo as parameter
        handle :: (s ~ RealWorld)
               => (D.CekTrans uni fun ann s, ExBudgetInfo ExBudget uni fun s)
               -> D.DebugF uni fun ann Breakpoints (IO ())
               -> IO ()
        handle (cekTrans, exBudgetInfo) = \case
          D.StepF prevState k  -> do
              stepRes <- liftCek $ D.tryError $ cekTrans prevState
              -- if error then handle it, otherwise "kontinue"
              case stepRes of
                  Left e         -> handleError exBudgetInfo e
                  Right newState -> k newState
          D.InputF k           -> handleInput >>= k
          D.LogF text k        -> handleLog text >> k
          D.UpdateClientF ds k -> handleUpdate exBudgetInfo ds >> k

        handleInput = takeMVar driverMailbox

        handleUpdate exBudgetInfo cekState = do
            bd <- readBudgetData exBudgetInfo
            B.writeBChan brickMailbox $ UpdateClientEvent bd cekState

        handleError exBudgetInfo e = do
            bd <- readBudgetData exBudgetInfo
            B.writeBChan brickMailbox $ ErrorEvent bd e
            -- no kontinuation in case of error, the driver thread exits
            -- FIXME: decide what should happen after the error occurs
            -- e.g. a user dialog to (r)estart the thread with a button

        handleLog = B.writeBChan brickMailbox . LogEvent

        readBudgetData :: ExBudgetInfo ExBudget uni fun RealWorld -> IO BudgetData
        readBudgetData (ExBudgetInfo _ final cumulative) =
            stToIO (BudgetData <$> cumulative <*> (for mbudget $ const final))

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
