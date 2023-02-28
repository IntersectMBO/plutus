{-# LANGUAGE BangPatterns              #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE ImplicitParams            #-}
{-# LANGUAGE LambdaCase                #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE OverloadedStrings         #-}
{-# LANGUAGE TypeApplications          #-}
{-# LANGUAGE TypeSynonymInstances      #-}

{-# OPTIONS_GHC -Wno-orphans #-}
module Main (main) where

import PlutusCore qualified as PLC
import PlutusCore.Annotation
import PlutusCore.Evaluation.Machine.ExBudget (ExBudget (..), ExRestrictingBudget (..))
import PlutusCore.Evaluation.Machine.ExBudgetingDefaults qualified as PLC
import PlutusCore.Evaluation.Machine.ExMemory (ExCPU (..), ExMemory (..))
import PlutusCore.Evaluation.Machine.MachineParameters
import PlutusCore.Executable.Common
import PlutusCore.Executable.Parsers

import Data.Foldable
import Data.List (nub)
import Data.List.Split (splitOn)
import Data.Text qualified as T
import PlutusPrelude

import UntypedPlutusCore qualified as UPLC
import UntypedPlutusCore.DeBruijn
import UntypedPlutusCore.Evaluation.Machine.Cek qualified as Cek

import Control.DeepSeq (rnf)
import Control.Monad.Except
import Options.Applicative
import System.Exit (exitFailure)
import System.IO (hPrint, stderr)
import Text.Read (readMaybe)

import Control.Monad.ST (RealWorld)
import System.Console.Haskeline qualified as Repl
import UntypedPlutusCore.Evaluation.Machine.Cek.Debug.Driver qualified as D
import UntypedPlutusCore.Evaluation.Machine.Cek.Debug.Internal qualified as D

uplcHelpText :: String
uplcHelpText = helpText "Untyped Plutus Core"

uplcInfoCommand :: ParserInfo Command
uplcInfoCommand = plutus uplcHelpText

data BudgetMode  = Silent
                 | Verbose SomeBudgetMode

data SomeBudgetMode =
    forall cost. (Eq cost, NFData cost, PrintBudgetState cost) =>
        SomeBudgetMode (Cek.ExBudgetMode cost PLC.DefaultUni PLC.DefaultFun)

data EvalOptions =
    EvalOptions Input Format PrintMode BudgetMode TraceMode Output TimingMode CekModel

data DbgOptions =
    DbgOptions Input Format CekModel

---------------- Main commands -----------------

data Command = Apply     ApplyOptions
             | Convert   ConvertOptions
             | Optimise  OptimiseOptions
             | Print     PrintOptions
             | Example   ExampleOptions
             | Eval      EvalOptions
             | Dbg       DbgOptions
             | DumpModel
             | PrintBuiltinSignatures

---------------- Option parsers ----------------

cekmodel :: Parser CekModel
cekmodel =
    flag Default Unit
        (  short '1'
        <> long "unit-cek-model"
        <> help "Use unit AST node costs and builtin costs for CEK cost model (tallying mode only)"
        )

evalOpts :: Parser EvalOptions
evalOpts =
  EvalOptions <$>
    input <*> inputformat <*>
        printmode <*> budgetmode <*> tracemode <*> output <*> timingmode <*> cekmodel

dbgOpts :: Parser DbgOptions
dbgOpts =
  DbgOptions <$>
    input <*> inputformat <*> cekmodel

-- Reader for budget.  The --restricting option requires two integer arguments
-- and the easiest way to do this is to supply a colon-separated pair of
-- integers.
exbudgetReader :: ReadM ExBudget
exbudgetReader = do
  s <- str
  case splitOn ":" s of
    [a,b] -> case (readMaybe a, readMaybe b) of
               (Just cpu, Just mem) -> pure $ ExBudget (ExCPU cpu) (ExMemory mem)
               _                    -> readerError badfmt
    _     -> readerError badfmt
    where badfmt = "Invalid budget (expected eg 10000:50000)"

restrictingbudgetEnormous :: Parser BudgetMode
restrictingbudgetEnormous =
    flag' (Verbose $ SomeBudgetMode Cek.restrictingEnormous)
        (  long "restricting-enormous"
        <> short 'r'
        <> help "Run the machine in restricting mode with an enormous budget" )

restrictingbudget :: Parser BudgetMode
restrictingbudget =
    Verbose . SomeBudgetMode . Cek.restricting . ExRestrictingBudget
        <$> option exbudgetReader
                (  long "restricting"
                <> short 'R'
                <> metavar "ExCPU:ExMemory"
                <> help "Run the machine in restricting mode with the given limits" )

countingbudget :: Parser BudgetMode
countingbudget = flag' (Verbose $ SomeBudgetMode Cek.counting)
                 (  long "counting"
                 <> short 'c'
                 <> help "Run machine in counting mode and report results" )

tallyingbudget :: Parser BudgetMode
tallyingbudget = flag' (Verbose $ SomeBudgetMode Cek.tallying)
                 (  long "tallying"
                 <> short 't'
                 <> help "Run machine in tallying mode and report results" )

budgetmode :: Parser BudgetMode
budgetmode = asum
    [ restrictingbudgetEnormous
    , restrictingbudget
    , countingbudget
    , tallyingbudget
    , pure Silent
    ]

plutus ::
  -- | The @helpText@
  String ->
  ParserInfo Command
plutus langHelpText =
    info
      (plutusOpts <**> helper)
      (fullDesc <> header "Untyped Plutus Core Tool" <> progDesc langHelpText)

plutusOpts :: Parser Command
plutusOpts = hsubparser $
       command "apply"
           (info (Apply <$> applyOpts)
            (progDesc $ "Given a list of input scripts f g1 g2 ... gn, " <>
            "output a script consisting of (... ((f g1) g2) ... gn); " <>
            "for example, 'uplc apply --if " <>
            "flat Validator.flat Datum.flat Redeemer.flat Context.flat --of flat -o Script.flat'"))
    <> command "print"
           (info (Print <$> printOpts)
            (progDesc "Parse a program then prettyprint it."))
    <> command "convert"
           (info (Convert <$> convertOpts)
            (progDesc "Convert a program between various formats"))
    <> command "optimise"
           (info (Optimise <$> optimiseOpts)
            (progDesc "Run the UPLC optimisation pipeline on the input"))
    <> command "optimize"
           (info (Optimise <$> optimiseOpts)
            (progDesc "Run the UPLC optimisation pipeline on the input"))
    <> command "example"
           (info (Example <$> exampleOpts)
            (progDesc $ "Show a program example. "
                     ++ "Usage: first request the list of available examples (optional step), "
                     ++ "then request a particular example by the name of a term. "
                     ++ "Note that evaluating a generated example may result in 'Failure'."))
    <> command "evaluate"
           (info (Eval <$> evalOpts)
            (progDesc "Evaluate an untyped Plutus Core program using the CEK machine."))
    <> command "debug"
           (info (Dbg <$> dbgOpts)
            (progDesc "Debug an untyped Plutus Core program using the CEK machine."))
    <> command "dump-model"
           (info (pure DumpModel)
            (progDesc "Dump the cost model parameters"))
    <> command "print-builtin-signatures"
           (info (pure PrintBuiltinSignatures)
            (progDesc "Print the signatures of the built-in functions"))


---------------- Optimisation ----------------

-- | Run the UPLC optimisations
runOptimisations:: OptimiseOptions -> IO ()
runOptimisations (OptimiseOptions inp ifmt outp ofmt mode) = do
    prog <- readProgram ifmt inp :: IO (UplcProg SrcSpan)
    simplified <- PLC.runQuoteT $ do
                    renamed <- PLC.rename prog
                    UPLC.simplifyProgram UPLC.defaultSimplifyOpts renamed
    writeProgram outp ofmt mode simplified

---------------- Script application ----------------

-- | Apply one script to a list of others.
runApply :: ApplyOptions -> IO ()
runApply (ApplyOptions inputfiles ifmt outp ofmt mode) = do
  scripts <-
    mapM ((readProgram ifmt ::  Input -> IO (UplcProg SrcSpan)) . FileInput) inputfiles
  let appliedScript =
        case void <$> scripts of
          []          -> errorWithoutStackTrace "No input files"
          progAndargs -> foldl1 UPLC.applyProgram progAndargs
  writeProgram outp ofmt mode appliedScript

---------------- Evaluation ----------------

runEval :: EvalOptions -> IO ()
runEval (EvalOptions inp ifmt printMode budgetMode traceMode outputMode timingMode cekModel) = do
    prog <- readProgram ifmt inp
    let term = void $ prog ^. UPLC.progTerm
        !_ = rnf term
        cekparams = case cekModel of
                    -- AST nodes are charged according to the default cost model
                    Default -> PLC.defaultCekParameters
                    -- AST nodes are charged one unit each, so we can see how many times each node
                    -- type is encountered.  This is useful for calibrating the budgeting code
                    Unit    -> PLC.unitCekParameters
    let budgetM = case budgetMode of
            Silent     -> SomeBudgetMode Cek.restrictingEnormous
            Verbose bm -> bm
    let emitM = case traceMode of
            None               -> Cek.noEmitter
            Logs               -> Cek.logEmitter
            LogsWithTimestamps -> Cek.logWithTimeEmitter
            LogsWithBudgets    -> Cek.logWithBudgetEmitter
    -- Need the existential cost type in scope
    case budgetM of
        SomeBudgetMode bm -> evalWithTiming term >>= handleResults term
            where
                evaluate = Cek.runCek cekparams bm emitM
                evalWithTiming t = case timingMode of
                        NoTiming -> pure $ evaluate t
                        Timing n -> do
                            rs <- timeEval n evaluate t
                            case nub rs of
                                [a] -> pure a
                                _   -> error "Timing evaluations returned inconsistent results"
                handleResults t (res, budget, logs) = do
                    case res of
                        Left err -> hPrint stderr err >> exitFailure
                        Right v  -> writeToFileOrStd outputMode (show (getPrintMethod printMode v))
                    case budgetMode of
                        Silent    -> pure ()
                        Verbose _ -> printBudgetState t cekModel budget
                    case traceMode of
                        None -> pure ()
                        _    -> writeToFileOrStd outputMode (T.unpack (T.intercalate "\n" logs))

---------------- Debugging ----------------

runDbg :: DbgOptions -> IO ()
runDbg (DbgOptions inp ifmt cekModel) = do
    prog <- readProgram ifmt inp
    let term = prog ^. UPLC.progTerm
        !_ = rnf term
        nterm = fromRight (error "Term to debug must be closed.") $
                   runExcept @FreeVariableError $ deBruijnTerm term
    let cekparams = case cekModel of
                    -- AST nodes are charged according to the default cost model
                    Default -> PLC.defaultCekParameters
                    -- AST nodes are charged one unit each, so we can see how many times each node
                    -- type is encountered.  This is useful for calibrating the budgeting code
                    Unit    -> PLC.unitCekParameters
        MachineParameters costs runtime = cekparams
    let ?cekRuntime = runtime
        ?cekEmitter = const $ pure ()
        ?cekBudgetSpender = Cek.CekBudgetSpender $ \_ _ -> pure ()
        ?cekCosts = costs
        ?cekSlippage = D.defaultSlippage
      in Repl.runInputT (Repl.Settings Repl.noCompletion Nothing False) $
            -- MAYBE: use cutoff or partialIterT to prevent runaway
            D.iterTM handleDbg $ D.runDriver nterm

-- only using one breakpoint at a time allowed at the moment
type Breakpoints = SrcSpan
type DAnn = SrcSpan
instance D.Breakpointable DAnn Breakpoints where
    hasBreakpoints = error "Not implemented: Breakpointable DAnn Breakpoints"

-- Peel off one layer
handleDbg :: (Cek.PrettyUni uni fun, D.GivenCekReqs uni fun DAnn RealWorld)
          => D.DebugF uni fun DAnn Breakpoints (Repl.InputT IO a)
          -> Repl.InputT IO a
handleDbg = \case
    -- Note that we first turn Cek to IO and then `liftIO` it to InputT; the alternative of
    -- directly using MonadTrans.lift needs MonadCatch+MonadMask instances for CekM, i.e. messy
    D.StepF prevState k  -> liftIO (D.cekMToIO $ D.handleStep prevState) >>= k
    D.InputF k           -> handleInput >>= k
    D.LogF text k        -> handleLog text >> k
    D.UpdateClientF ds k -> handleUpdate ds >> k
  where
    handleInput = error "Not implemented: handleInput"
    handleUpdate _s = Repl.outputStrLn "UPDATETUI" -- TODO: implement
    handleLog = Repl.outputStrLn

----------------- Print examples -----------------------
runUplcPrintExample ::
    ExampleOptions -> IO ()
runUplcPrintExample = runPrintExample getUplcExamples

---------------- Driver ----------------

main :: IO ()
main = do
    options <- customExecParser (prefs showHelpOnEmpty) uplcInfoCommand
    case options of
        Apply     opts         -> runApply             opts
        Eval      opts         -> runEval              opts
        Dbg       opts         -> runDbg               opts
        Example   opts         -> runUplcPrintExample  opts
        Optimise  opts         -> runOptimisations     opts
        Print     opts         -> runPrint   @UplcProg opts
        Convert   opts         -> runConvert @UplcProg opts
        DumpModel              -> runDumpModel
        PrintBuiltinSignatures -> runPrintBuiltinSignatures
