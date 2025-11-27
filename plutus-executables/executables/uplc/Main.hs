-- editorconfig-checker-disable
{-# OPTIONS_GHC -Wno-orphans #-}

module Main (main) where

import PlutusCore qualified as PLC
import PlutusCore.Annotation (SrcSpan)
import PlutusCore.Data (Data)
import PlutusCore.Default (BuiltinSemanticsVariant (..))
import PlutusCore.Evaluation.Machine.ExBudget (ExBudget (..), ExRestrictingBudget (..))
import PlutusCore.Evaluation.Machine.ExBudgetingDefaults qualified as PLC
import PlutusCore.Evaluation.Machine.ExMemory (ExCPU (..), ExMemory (..))
import PlutusCore.Executable.AstIO (toDeBruijnTermUPLC)
import PlutusCore.Executable.Common
import PlutusCore.Executable.Parsers
import PlutusCore.MkPlc (mkConstant)
import PlutusPrelude

import UntypedPlutusCore.Evaluation.Machine.SteppableCek.DebugDriver qualified as D
import UntypedPlutusCore.Evaluation.Machine.SteppableCek.Internal qualified as D

import UntypedPlutusCore qualified as UPLC
import UntypedPlutusCore.DeBruijn (FreeVariableError)
import UntypedPlutusCore.Evaluation.Machine.Cek qualified as Cek

import Codec.Serialise (DeserialiseFailure, deserialiseOrFail)
import Control.DeepSeq (force)
import Control.Monad.Except
import Control.Monad.IO.Class (liftIO)
import Criterion (benchmarkWith, whnf)
import Criterion.Main (defaultConfig)
import Criterion.Types (Config (..))
import Data.ByteString.Lazy as BSL (readFile)
import Data.Foldable
import Data.List.Split (splitOn)
import Data.Text qualified as T
import Options.Applicative
import PlutusCore.Flat (unflat)
import Prettyprinter ((<+>))
import System.Exit (ExitCode (..), exitFailure, exitSuccess, exitWith)
import System.IO (hPrint, stderr)
import Text.Read (readMaybe)

import Control.Monad.ST (RealWorld)
import System.Console.Haskeline qualified as Repl

import Data.Version.Extras (gitAwareVersionInfo)
import Paths_plutus_executables qualified as Paths

import Certifier

uplcHelpText :: String
uplcHelpText = helpText "Untyped Plutus Core"

uplcInfoCommand :: ParserInfo Command
uplcInfoCommand = plutus uplcHelpText

data BudgetMode
  = Silent
  | Verbose SomeBudgetMode

data SomeBudgetMode
  = forall cost.
    (Eq cost, NFData cost, PrintBudgetState cost) =>
    SomeBudgetMode (Cek.ExBudgetMode cost PLC.DefaultUni PLC.DefaultFun)

data EvalOptions
  = EvalOptions
      Input
      Format
      PrintMode
      NameFormat
      BudgetMode
      TraceMode
      Output
      CekModel
      (BuiltinSemanticsVariant PLC.DefaultFun)

data BenchmarkOptions
  = BenchmarkOptions
      Input
      Format
      (BuiltinSemanticsVariant PLC.DefaultFun)
      Double

data DbgOptions
  = DbgOptions
      Input
      Format
      CekModel
      (BuiltinSemanticsVariant PLC.DefaultFun)

---------------- Main commands -----------------

data Command
  = Apply ApplyOptions
  | ApplyToFlatData ApplyOptions
  | ApplyToCborData ApplyOptions
  | Benchmark BenchmarkOptions
  | Convert ConvertOptions
  | Optimise OptimiseOptions
  | Print PrintOptions
  | Example ExampleOptions
  | Eval EvalOptions
  | Dbg DbgOptions
  | DumpModel (BuiltinSemanticsVariant PLC.DefaultFun)
  | PrintBuiltinSignatures

---------------- Option parsers ----------------

cekmodel :: Parser CekModel
cekmodel =
  flag
    Default
    Unit
    ( short '1'
        <> long "unit-cek-model"
        <> help "Use unit AST node costs and builtin costs for CEK cost model (tallying mode only)"
    )

benchmarkOpts :: Parser BenchmarkOptions
benchmarkOpts =
  BenchmarkOptions
    <$> input
    <*> inputformat
    <*> builtinSemanticsVariant
    <*> option
      auto
      ( long "time-limit"
          <> short 'T'
          <> metavar "TIME LIMIT"
          <> value 5.0
          <> showDefault
          <> help "Time limit (in seconds) for benchmarking."
      )

evalOpts :: Parser EvalOptions
evalOpts =
  EvalOptions
    <$> input
    <*> inputformat
    <*> printmode
    <*> nameformat
    <*> budgetmode
    <*> tracemode
    <*> output
    <*> cekmodel
    <*> builtinSemanticsVariant

dbgOpts :: Parser DbgOptions
dbgOpts =
  DbgOptions
    <$> input
    <*> inputformat
    <*> cekmodel
    <*> builtinSemanticsVariant

-- Reader for budget.  The --restricting option requires two integer arguments
-- and the easiest way to do this is to supply a colon-separated pair of
-- integers.
exbudgetReader :: ReadM ExBudget
exbudgetReader = do
  s <- str
  case splitOn ":" s of
    [a, b] -> case (readMaybe a, readMaybe b) of
      (Just cpu, Just mem) -> pure $ ExBudget (ExCPU cpu) (ExMemory mem)
      _ -> readerError badfmt
    _ -> readerError badfmt
  where
    badfmt = "Invalid budget (expected eg 10000:50000)"

restrictingbudgetEnormous :: Parser BudgetMode
restrictingbudgetEnormous =
  flag'
    (Verbose $ SomeBudgetMode Cek.restrictingEnormous)
    ( long "restricting-enormous"
        <> short 'r'
        <> help "Run the machine in restricting mode with an enormous budget"
    )

restrictingbudget :: Parser BudgetMode
restrictingbudget =
  Verbose . SomeBudgetMode . Cek.restricting . ExRestrictingBudget
    <$> option
      exbudgetReader
      ( long "restricting"
          <> short 'R'
          <> metavar "ExCPU:ExMemory"
          <> help "Run the machine in restricting mode with the given limits"
      )

countingbudget :: Parser BudgetMode
countingbudget =
  flag'
    (Verbose $ SomeBudgetMode Cek.counting)
    ( long "counting"
        <> short 'c'
        <> help "Run machine in counting mode and report results"
    )

tallyingbudget :: Parser BudgetMode
tallyingbudget =
  flag'
    (Verbose $ SomeBudgetMode Cek.tallying)
    ( long "tallying"
        <> short 't'
        <> help "Run machine in tallying mode and report results"
    )

budgetmode :: Parser BudgetMode
budgetmode =
  asum
    [ restrictingbudgetEnormous
    , restrictingbudget
    , countingbudget
    , tallyingbudget
    , pure Silent
    ]

plutus
  :: String
  -- ^ The @helpText@
  -> ParserInfo Command
plutus langHelpText =
  info
    (plutusOpts <**> versioner <**> helper)
    (fullDesc <> header "Untyped Plutus Core Tool" <> progDesc langHelpText)

plutusOpts :: Parser Command
plutusOpts =
  hsubparser $
    command
      "apply"
      ( info
          (Apply <$> applyOpts)
          ( progDesc $
              "Given a list of input files f g1 g2 ... gn "
                <> "containing Untyped Plutus Core scripts, "
                <> "output a script consisting of (... ((f g1) g2) ... gn); "
                <> "for example, 'uplc apply --if flat Validator.flat "
                <> "Datum.flat Redeemer.flat Context.flat --of flat -o Script.flat'."
          )
      )
      <> command
        "apply-to-flat-data"
        ( info
            (ApplyToFlatData <$> applyOpts)
            ( progDesc $
                "Given a list f d1 d2 ... dn where f is an "
                  <> "Untyped Plutus Core script and d1,...,dn are files "
                  <> "containing flat-encoded data ojbects, output a script "
                  <> "consisting of f applied to the data objects; "
                  <> "for example, 'uplc apply-to-flat-data --if "
                  <> "flat Validator.flat Datum.flat Redeemer.flat Context.flat "
                  <> "--of flat -o Script.flat'."
            )
        )
      <> command
        "apply-to-cbor-data"
        ( info
            (ApplyToCborData <$> applyOpts)
            ( progDesc $
                "Given a list f d1 d2 ... dn where f is an "
                  <> "Untyped Plutus Core script and d1,...,dn are files "
                  <> "containing CBOR-encoded data ojbects, output a script "
                  <> "consisting of f applied to the data objects; "
                  <> "for example, 'uplc apply-to-cbor-data --if "
                  <> "flat Validator.flat Datum.cbor Redeemer.cbor Context.cbor "
                  <> "--of flat -o Script.flat'."
            )
        )
      <> command
        "print"
        ( info
            (Print <$> printOpts)
            (progDesc "Parse a program then prettyprint it.")
        )
      <> command
        "convert"
        ( info
            (Convert <$> convertOpts)
            (progDesc "Convert a program between various formats.")
        )
      <> command "optimise" (optimise "Run the UPLC optimisation pipeline on the input.")
      <> command "optimize" (optimise "Same as 'optimise'.")
      <> command
        "example"
        ( info
            (Example <$> exampleOpts)
            ( progDesc $
                "Show a program example. "
                  ++ "Usage: first request the list of available examples (optional step), "
                  ++ "then request a particular example by the name of a term. "
                  ++ "Note that evaluating a generated example may result in 'Failure'."
            )
        )
      <> command
        "benchmark"
        ( info
            (Benchmark <$> benchmarkOpts)
            (progDesc "Benchmark an untyped Plutus Core program on the CEK machine using Criterion.")
        )
      <> command
        "evaluate"
        ( info
            (Eval <$> evalOpts)
            (progDesc "Evaluate an untyped Plutus Core program using the CEK machine.")
        )
      <> command
        "debug"
        ( info
            (Dbg <$> dbgOpts)
            (progDesc "Debug an untyped Plutus Core program using the CEK machine.")
        )
      <> command
        "dump-cost-model"
        ( info
            (DumpModel <$> builtinSemanticsVariant)
            (progDesc "Dump the cost model parameters.")
        )
      <> command
        "print-builtin-signatures"
        ( info
            (pure PrintBuiltinSignatures)
            (progDesc "Print the signatures of the built-in functions.")
        )
  where
    optimise desc = info (Optimise <$> optimiseOpts) $ progDesc desc

---------------- Optimisation ----------------

-- | Run the UPLC optimisations
runOptimisations :: OptimiseOptions -> IO ()
runOptimisations (OptimiseOptions inp ifmt outp ofmt mode mcert) = do
  prog <- readProgram ifmt inp :: IO (UplcProg SrcSpan)
  (simplified, simplificationTrace) <- PLC.runQuoteT $ do
    renamed <- PLC.rename prog
    let defaultBuiltinSemanticsVariant :: BuiltinSemanticsVariant PLC.DefaultFun
        defaultBuiltinSemanticsVariant = def
    UPLC.simplifyProgramWithTrace UPLC.defaultSimplifyOpts defaultBuiltinSemanticsVariant renamed
  writeProgram outp ofmt mode simplified
  case mcert of
    Nothing -> pure ()
    Just cert -> execCertifier simplificationTrace cert
  where
    execCertifier simplificationTrace cert = do
      result <- runCertifier $ mkCertifier simplificationTrace cert
      case result of
        Left err -> do
          putStrLn $ prettyCertifierError err
          case err of
            InvalidCertificate _ -> exitWith $ ExitFailure 1
            InvalidCompilerOutput -> exitWith $ ExitFailure 2
            ValidationError _ -> exitWith $ ExitFailure 3
        Right certSucc -> do
          putStrLn $ prettyCertifierSuccess certSucc
          exitSuccess

---------------- Script application ----------------

{-| Apply one script to a list of others and output the result.  All of the
scripts must be UPLC.Program objects. -}
runApply :: ApplyOptions -> IO ()
runApply (ApplyOptions inputfiles ifmt outp ofmt mode) = do
  scripts <- mapM ((readProgram ifmt :: Input -> IO (UplcProg SrcSpan)) . FileInput) inputfiles
  let appliedScript =
        case void <$> scripts of
          [] -> errorWithoutStackTrace "No input files"
          progAndargs ->
            foldl1 (unsafeFromRight .* UPLC.applyProgram) progAndargs
  writeProgram outp ofmt mode appliedScript

{-| Apply a UPLC program to script to a list of flat-encoded Data objects and
output the result. -}
runApplyToFlatData :: ApplyOptions -> IO ()
runApplyToFlatData (ApplyOptions inputfiles ifmt outp ofmt mode) =
  case inputfiles of
    [] -> errorWithoutStackTrace "No input files"
    p : ds -> do
      prog@(UPLC.Program _ version _) :: UplcProg SrcSpan <- readProgram ifmt (FileInput p)
      args <- mapM (getDataObject version) ds
      let prog' = void prog
          appliedScript = foldl1 (unsafeFromRight .* UPLC.applyProgram) (prog' : args)
      writeProgram outp ofmt mode appliedScript
      where
        getDataObject :: UPLC.Version -> FilePath -> IO (UplcProg ())
        getDataObject ver path = do
          bs <- BSL.readFile path
          case unflat bs of
            Left err -> fail ("Error reading " ++ show path ++ ": " ++ show err)
            Right (d :: Data) -> pure $ UPLC.Program () ver $ mkConstant () d

{-| Apply a UPLC program to script to a list of CBOR-encoded flat-encoded Data
objects and output the result. -}
runApplyToCborData :: ApplyOptions -> IO ()
runApplyToCborData (ApplyOptions inputfiles ifmt outp ofmt mode) =
  case inputfiles of
    [] -> errorWithoutStackTrace "No input files"
    p : ds -> do
      prog@(UPLC.Program _ version _) :: UplcProg SrcSpan <- readProgram ifmt (FileInput p)
      args <- mapM (getCborDataObject version) ds
      let prog' = void prog
          appliedScript = foldl1 (unsafeFromRight .* UPLC.applyProgram) (prog' : args)
      writeProgram outp ofmt mode appliedScript
      where
        getCborDataObject :: UPLC.Version -> FilePath -> IO (UplcProg ())
        getCborDataObject ver path = do
          bs <- BSL.readFile path
          case deserialiseOrFail bs :: Either DeserialiseFailure Data of
            Left err -> fail ("Cannot decode CBOR object " ++ show path ++ ":" ++ show err)
            Right d -> pure $ UPLC.Program () ver $ mkConstant () d

---------------- Benchmarking ----------------

runBenchmark :: BenchmarkOptions -> IO ()
runBenchmark (BenchmarkOptions inp ifmt semvar timeLim) = do
  prog <- readProgram ifmt inp
  let criterionConfig = defaultConfig {reportFile = Nothing, timeLimit = timeLim}
      cekparams = PLC.defaultCekParametersForVariant semvar
      -- Extract an evaluation result
      getResult = either (error . show) (const ()) . Cek.cekResultToEither . Cek._cekReportResult
      evaluate = getResult . Cek.runCekDeBruijn cekparams Cek.restrictingEnormous Cek.noEmitter
      -- readProgam throws away De Bruijn indices and returns an AST with Names;
      -- we have to put them back to get an AST with NamedDeBruijn names.
      !term =
        fromRight (error "Unexpected open term in runBenchmark.")
          . runExcept @FreeVariableError
          $ UPLC.deBruijnTerm (UPLC._progTerm prog)
      -- Big names slow things down
      !anonTerm = UPLC.termMapNames (\(PLC.NamedDeBruijn _ i) -> PLC.NamedDeBruijn "" i) term
      -- Big annotations slow things down
      !unitAnnTerm = force (void anonTerm)
  benchmarkWith criterionConfig $! whnf evaluate unitAnnTerm

---------------- Evaluation ----------------

runEval :: EvalOptions -> IO ()
runEval
  ( EvalOptions
      inp
      ifmt
      printMode
      nameFormat
      budgetMode
      traceMode
      outp
      cekModel
      semvar
    ) = do
    prog <- readProgram ifmt inp
    let term = void $ prog ^. UPLC.progTerm

        cekparams = case cekModel of
          -- AST nodes are charged according to the default cost model
          Default -> PLC.defaultCekParametersForVariant semvar
          -- AST nodes are charged one unit each, so we can see how many times each node
          -- type is encountered.  This is useful for calibrating the budgeting code
          Unit -> PLC.unitCekParameters
    let emitM = case traceMode of
          None -> Cek.noEmitter
          Logs -> Cek.logEmitter
          LogsWithTimestamps -> Cek.logWithTimeEmitter
          LogsWithBudgets -> Cek.logWithBudgetEmitter
          LogsWithCallTrace -> Cek.logWithCallTraceEmitter
    -- Need the existential cost type in scope
    let budgetM = case budgetMode of
          Silent -> SomeBudgetMode Cek.restrictingEnormous
          Verbose bm -> bm
    case budgetM of
      SomeBudgetMode bm ->
        do
          let Cek.CekReport res budget logs = Cek.runCek cekparams bm emitM term
          case Cek.cekResultToEither res of
            Left err -> hPrint stderr err
            Right v ->
              case nameFormat of
                IdNames -> writeToOutput outp $ prettyPrintByMode printMode v
                DeBruijnNames -> writeToOutput outp $ prettyPrintByMode printMode $ toDeBruijnTermUPLC v
          case budgetMode of
            Silent -> pure ()
            Verbose _ -> printBudgetState term cekModel budget
          case traceMode of
            None -> pure ()
            _ -> writeToOutput outp (T.intercalate "\n" logs)
          case Cek.cekResultToEither res of
            Left _ -> exitFailure
            Right _ -> pure ()

---------------- Debugging ----------------

runDbg :: DbgOptions -> IO ()
runDbg (DbgOptions inp ifmt cekModel semvar) = do
  prog <- readProgram ifmt inp
  let term = prog ^. UPLC.progTerm
      nterm =
        fromRight (error "Term to debug must be closed.") $
          runExcept @FreeVariableError $
            UPLC.deBruijnTerm term
  let cekparams = case cekModel of
        -- AST nodes are charged according to the appropriate cost model
        Default -> PLC.defaultCekParametersForVariant semvar
        -- AST nodes are charged one unit each, so we can see how many times each node
        -- type is encountered.  This is useful for calibrating the budgeting code
        Unit -> PLC.unitCekParameters
      replSettings =
        Repl.Settings
          { Repl.complete = Repl.noCompletion
          , Repl.historyFile = Nothing
          , Repl.autoAddHistory = False
          }
  -- nilSlippage is important so as to get correct live up-to-date budget
  cekTrans <- fst <$> D.mkCekTrans cekparams Cek.restrictingEnormous Cek.noEmitter D.nilSlippage
  Repl.runInputT replSettings $
    D.iterTM (handleDbg cekTrans) $
      D.runDriverT nterm

-- TODO: this is just an example of an optional single breakpoint, decide
-- if we actually want breakpoints for the cli
newtype MaybeBreakpoint = MaybeBreakpoint {_fromMaybeBreakpoint :: Maybe SrcSpan}
type DAnn = SrcSpan
instance D.Breakpointable DAnn MaybeBreakpoint where
  hasBreakpoints = error "Not implemented: Breakpointable DAnn Breakpoints"

-- Peel off one layer
handleDbg
  :: Cek.ThrowableBuiltins uni fun
  => D.CekTrans uni fun DAnn RealWorld
  -> D.DebugF uni fun DAnn MaybeBreakpoint (Repl.InputT IO ())
  -> Repl.InputT IO ()
handleDbg cekTrans = \case
  D.StepF prevState k -> do
    -- Note that we first turn Cek to IO and then `liftIO` it to InputT; the alternative of
    -- directly using MonadTrans.lift needs MonadCatch+MonadMask instances for CekM, i.e. messy
    -- also liftIO would be unnecessary if haskeline.InputT worked with `primitive`
    eNewState <- liftIO $ D.liftCek $ tryError $ cekTrans prevState
    case eNewState of
      Right newState -> k newState
      Left e -> Repl.outputStrLn $ show e
  -- no continuation, so it acts like exitSuccess
  -- FIXME: decide what should happen after the error occurs
  D.InputF k -> handleInput >>= k
  D.DriverLogF text k -> handleLog text >> k
  D.UpdateClientF ds k -> handleUpdate ds >> k
  where
    handleInput = do
      c <- Repl.getInputChar "(s)tep (c)ontinue (n)ext (f)inish (Ctrl+d exit):"
      -- TODO: implement print "program counter", breakpoints
      -- MAYBE: switch to repline
      case c of
        Just 's' -> pure D.Step
        Just 'c' -> pure $ D.Continue $ MaybeBreakpoint empty
        Just 'n' -> pure $ D.Next $ MaybeBreakpoint empty
        Just 'f' -> pure $ D.Finish $ MaybeBreakpoint empty
        -- otherwise retry
        _ -> handleInput
    handleUpdate s = Repl.outputStrLn $ show $ "Updated state:" <+> pretty s
    handleLog = Repl.outputStrLn . T.unpack

----------------- Print examples -----------------------
runUplcPrintExample
  :: ExampleOptions -> IO ()
runUplcPrintExample = runPrintExample getUplcExamples

----------------- Version -----------------------

versioner :: Parser (a -> a)
versioner = simpleVersioner (gitAwareVersionInfo Paths.version)

---------------- Driver ----------------

main :: IO ()
main = do
  options <- customExecParser (prefs showHelpOnEmpty) uplcInfoCommand
  case options of
    Apply opts -> runApply opts
    ApplyToFlatData opts -> runApplyToFlatData opts
    ApplyToCborData opts -> runApplyToCborData opts
    Benchmark opts -> runBenchmark opts
    Eval opts -> runEval opts
    Dbg opts -> runDbg opts
    Example opts -> runUplcPrintExample opts
    Optimise opts -> runOptimisations opts
    Print opts -> runPrint @UplcProg opts
    Convert opts -> runConvert @UplcProg opts
    DumpModel opts -> runDumpModel opts
    PrintBuiltinSignatures -> runPrintBuiltinSignatures
