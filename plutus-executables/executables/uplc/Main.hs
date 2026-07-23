{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Main (main) where

import PlutusCore qualified as PLC
import PlutusCore.Annotation (SrcSpan)
import PlutusCore.Data (Data)
import PlutusCore.Default
  ( BuiltinSemanticsVariant (..)
  )
import PlutusCore.Evaluation.Machine.ExBudget
  ( ExBudget (..)
  , ExRestrictingBudget (..)
  )
import PlutusCore.Evaluation.Machine.ExBudgetingDefaults qualified as PLC
import PlutusCore.Evaluation.Machine.ExMemory
  ( ExCPU (..)
  , ExMemory (..)
  )
import PlutusCore.Executable.AstIO
  ( UplcTermNDB
  , toDeBruijnTermUPLC
  )
import PlutusCore.Executable.Blueprint
import PlutusCore.Executable.Common
import PlutusCore.Executable.Eval
import PlutusCore.Executable.Help qualified as Help
import PlutusCore.Executable.OptimizerReport
import PlutusCore.Executable.Parsers
import PlutusCore.MkPlc (mkConstant)
import PlutusPrelude
import UntypedPlutusCore qualified as UPLC
import UntypedPlutusCore.DeBruijn (FreeVariableError)
import UntypedPlutusCore.Evaluation.Machine.Cek qualified as Cek
import UntypedPlutusCore.Evaluation.Machine.SteppableCek.DebugDriver qualified as D
import UntypedPlutusCore.Evaluation.Machine.SteppableCek.Internal qualified as D

import Codec.Serialise
  ( DeserialiseFailure
  , deserialiseOrFail
  )
import Control.DeepSeq (force)
import Control.Exception (evaluate)
import Control.Monad.Except
  ( runExcept
  , tryError
  )
import Control.Monad.Extra (whenJust)
import Control.Monad.IO.Class (liftIO)
import Control.Monad.ST (RealWorld)
import Criterion
  ( benchmarkWith
  , whnf
  )
import Criterion.Main (defaultConfig)
import Criterion.Types (Config (..))
import Data.ByteString.Base16 qualified as Base16
import Data.ByteString.Lazy qualified as BSL
import Data.IORef
  ( newIORef
  , readIORef
  )
import Data.List.Split (splitOn)
import Data.Text qualified as T
import Data.Text.Encoding qualified as T
import Data.Text.IO qualified as T
import Data.Time.Clock.System
  ( getSystemTime
  , systemNanoseconds
  )
import Options.Applicative
import PlutusCore.Flat (unflat)
import Prettyprinter ((<+>))
import System.CPUTime (getCPUTime)
import System.Console.Haskeline qualified as Repl
import System.Directory.Extra (doesFileExist)
import System.Exit
  ( ExitCode (..)
  , exitFailure
  , exitWith
  )
import System.FilePath
import System.IO
  ( hPrint
  , stderr
  )
import System.Mem (performGC)
import Text.Printf (printf)
import Text.Read (readMaybe)

import Data.Version.Extras (gitAwareVersionInfo)
import Paths_plutus_executables qualified as Paths

import Certifier

uplcHelpText :: String
uplcHelpText = helpText "Untyped Plutus Core"

uplcInfoCommand :: ParserInfo Command
uplcInfoCommand = plutus uplcHelpText

topLevelExamples :: [Help.Example]
topLevelExamples =
  [ Help.eg
      "Evaluate a textual UPLC program on the CEK machine"
      "uplc evaluate -i program.uplc"
  , Help.eg
      "Evaluate a hex-encoded script and report the CPU/memory budget used"
      "uplc evaluate --if hex -i script.hex --counting"
  , Help.eg
      "Pretty-print a hex-encoded script as readable textual UPLC"
      "uplc convert --if hex --of textual -i script.hex"
  , Help.eg
      "Optimise a script"
      "uplc optimize -i program.uplc -o program-opt.uplc"
  , Help.eg
      "List the built-in example programs"
      "uplc example -a"
  , Help.eg
      "Enable bash completion for the current shell"
      "source <(uplc --bash-completion-script $(command -v uplc))"
  ]

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

data TimeEvalOptions
  = TimeEvalOptions
      Input
      Format
      (BuiltinSemanticsVariant PLC.DefaultFun)
      Integer -- number of repetitions
      Bool -- raw output (nanoseconds, no units)

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
  | Optimise (OptimiseOptions UPLC.Name SrcSpan)
  | Print PrintOptions
  | Example ExampleOptions
  | Eval EvalOptions
  | TimeEval TimeEvalOptions
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

timeOpts :: Parser TimeEvalOptions
timeOpts =
  TimeEvalOptions
    <$> input
    <*> inputformat
    <*> builtinSemanticsVariant
    <*> option
      auto
      ( short 'n'
          <> long "repeat"
          <> metavar "N"
          <> value 100
          <> showDefault
          <> help "Number of times to evaluate the script (average time is reported for N > 1)."
      )
    <*> switch
      ( long "raw"
          <> help "Print the average time in nanoseconds with no units."
      )

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
    ( fullDesc
        <> header "Untyped Plutus Core Tool"
        <> progDesc langHelpText
        <> Help.examplesFooter topLevelExamples
    )

plutusOpts :: Parser Command
plutusOpts =
  hsubparser $
    command
      "apply"
      ( info
          (Apply <$> applyOpts)
          ( progDesc
              ( "Given a list of input files f g1 g2 ... gn "
                  <> "containing Untyped Plutus Core scripts, "
                  <> "output a script consisting of (... ((f g1) g2) ... gn)."
              )
              <> Help.examplesFooter
                [ Help.eg
                    "Apply a flat-encoded validator to its arguments"
                    "uplc apply --if flat Validator.flat Datum.flat Redeemer.flat Context.flat --of flat -o Script.flat"
                ]
          )
      )
      <> command
        "apply-to-flat-data"
        ( info
            (ApplyToFlatData <$> applyOpts)
            ( progDesc
                ( "Given a list f d1 d2 ... dn where f is an "
                    <> "Untyped Plutus Core script and d1,...,dn are files "
                    <> "containing flat-encoded data objects, output a script "
                    <> "consisting of f applied to the data objects."
                )
                <> Help.examplesFooter
                  [ Help.eg
                      "Apply a script to flat-encoded Data arguments"
                      "uplc apply-to-flat-data --if flat Validator.flat Datum.flat Redeemer.flat Context.flat --of flat -o Script.flat"
                  ]
            )
        )
      <> command
        "apply-to-cbor-data"
        ( info
            (ApplyToCborData <$> applyOpts)
            ( progDesc
                ( "Given a list f d1 d2 ... dn where f is an "
                    <> "Untyped Plutus Core script and d1,...,dn are files "
                    <> "containing CBOR-encoded data objects, output a script "
                    <> "consisting of f applied to the data objects."
                )
                <> Help.examplesFooter
                  [ Help.eg
                      "Apply a script to CBOR-encoded Data arguments"
                      "uplc apply-to-cbor-data --if flat Validator.flat Datum.cbor Redeemer.cbor Context.cbor --of flat -o Script.flat"
                  ]
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
            ( progDesc "Convert a program between various formats."
                <> Help.examplesFooter
                  [ Help.eg
                      "Pretty-print a hex-encoded script as readable textual UPLC"
                      "uplc convert --if hex --of textual -i script.hex"
                  , Help.eg
                      "Flat-encode a textual UPLC program"
                      "uplc convert --if textual --of flat -i program.uplc -o program.flat"
                  ]
            )
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
            ( progDesc "Benchmark an untyped Plutus Core program on the CEK machine using Criterion."
                <> Help.examplesFooter
                  [ Help.eg
                      "Benchmark evaluation with a 20-second time limit"
                      "uplc benchmark -i program.uplc --time-limit 20"
                  ]
            )
        )
      <> command
        "evaluate"
        ( info
            (Eval <$> evalOpts)
            ( progDesc "Evaluate an untyped Plutus Core program using the CEK machine."
                <> Help.examplesFooter
                  [ Help.eg
                      "Evaluate a textual UPLC program"
                      "uplc evaluate -i program.uplc"
                  , Help.eg
                      "Evaluate a hex-encoded script and report the budget used"
                      "uplc evaluate --if hex -i script.hex --counting"
                  , Help.eg
                      "Evaluate a program piped in on stdin"
                      "echo '(program 1.1.0 (con integer 42))' | uplc evaluate"
                  ]
            )
        )
      <> command
        "time"
        ( info
            (TimeEval <$> timeOpts)
            ( progDesc $
                "Time the evaluation of an untyped Plutus Core program using the CEK machine.  "
                  ++ "For best results, bypass cabal and run the `uplc` binary directly; for example use `$(cabal list-bin uplc)`."
            )
        )
      <> command
        "debug"
        ( info
            (Dbg <$> dbgOpts)
            ( progDesc "Debug an untyped Plutus Core program using the CEK machine."
                <> Help.examplesFooter
                  [ Help.eg
                      "Step through a program interactively"
                      "uplc debug -i program.uplc"
                  ]
            )
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
    optimise desc =
      info (Optimise <$> optimiseOpts) $
        progDesc desc
          <> Help.examplesFooter
            [ Help.eg
                "Optimise a textual UPLC script"
                "uplc optimize -i program.uplc -o program-opt.uplc"
            , Help.eg
                "Optimise every validator in a CIP-57 blueprint"
                "uplc optimize --if blueprint --of blueprint -i bp.json -o bp-opt.json"
            ]

---------------- Optimisation ----------------

-- | Run the UPLC optimisations
runOptimisations :: OptimiseOptions UPLC.Name SrcSpan -> IO ()
runOptimisations (OptimiseOptions inp ifmt outp ofmt mode mcert certifierOutput sopts eopts) =
  case ifmt of
    Blueprint -> runOptimiseBlueprint inp outp ofmt mcert certifierOutput sopts eopts
    _ -> runOptimiseSingle inp ifmt outp ofmt mode mcert certifierOutput sopts eopts

runOptimiseSingle
  :: Input
  -> Format
  -> Output
  -> Format
  -> PrintMode
  -> Certifier
  -> CertifierOutputMode
  -> UPLC.OptimizeOpts UPLC.Name SrcSpan
  -> OptimiseEvalOpts
  -> IO ()
runOptimiseSingle inp ifmt outp ofmt mode mcert certifierOutput sopts eopts = do
  prog <- readProgram ifmt inp :: IO (UplcProg SrcSpan)
  (simplified, optimizerTrace) <- optimiseProgram sopts prog
  writeProgram outp ofmt mode simplified
  margs <- loadArgsIfEval eopts
  let costs = case margs of
        Nothing -> []
        Just args ->
          let evalCtx = mkDefaultEvalCtx def
           in evalOptimizerTrace evalCtx optimizerTrace args
  printReport stderr (buildReport optimizerTrace costs)
  whenJust mcert $ \cert -> do
    time <- systemNanoseconds <$> getSystemTime
    let certDir = cert <> "-" <> show time
        certOutput = case certifierOutput of
          CertBasic -> BasicOutput
          CertReport file -> ReportOutput file
          CertProject -> ProjectOutput certDir
    execCertifier optimizerTrace cert certOutput costs

runOptimiseBlueprint
  :: Input
  -> Output
  -> Format
  -> Certifier
  -> CertifierOutputMode
  -> UPLC.OptimizeOpts UPLC.Name SrcSpan
  -> OptimiseEvalOpts
  -> IO ()
runOptimiseBlueprint inp outp ofmt mcert certifierOutput sopts eopts
  | ofmt /= Blueprint = fail "When input format is blueprint, output format must also be blueprint."
  | otherwise = do
      (validators, blueprint) <- readBlueprint inp
      optimisedWithTrace <-
        traverse
          (optimiseProgram sopts . (topSrcSpan <$) . bvCode)
          validators
      let optimised = map (void . fst) optimisedWithTrace
          evalCtx = mkDefaultEvalCtx def
      writeBlueprint outp blueprint optimised
      time <- systemNanoseconds <$> getSystemTime
      for_ (zip validators (snd <$> optimisedWithTrace)) $ \(validator, optTrace) -> do
        let validatorName = T.unpack (bvTitle validator)
        margs <- loadBlueprintArgs eopts validatorName
        let costs = case margs of
              Nothing -> []
              Just args -> evalOptimizerTrace evalCtx optTrace args
        T.hPutStrLn stderr ("\n--- " <> bvTitle validator <> " ---")
        printReport stderr (buildReport optTrace costs)
        whenJust mcert $ \cert -> do
          let certDir = cert <> "-" <> validatorName <> "-" <> show time
              certOutput = case certifierOutput of
                CertBasic -> BasicOutput
                CertReport file ->
                  let (fileBase, fileExt) = splitExtension file
                   in ReportOutput (fileBase <> "-" <> validatorName <.> fileExt)
                CertProject -> ProjectOutput certDir
          execCertifier optTrace cert certOutput costs

optimiseProgram
  :: forall m name a
   . (UPLC.HasUnique name UPLC.TermUnique, Monad m, Ord name, Typeable name)
  => UPLC.OptimizeOpts name a
  -> UPLC.Program name UPLC.DefaultUni UPLC.DefaultFun a
  -> m
       ( UPLC.Program name UPLC.DefaultUni UPLC.DefaultFun a
       , UPLC.OptimizerTrace name UPLC.DefaultUni UPLC.DefaultFun a
       )
optimiseProgram opts prog = PLC.runQuoteT $ do
  renamed <- PLC.rename prog
  let defaultBuiltinSemanticsVariant :: BuiltinSemanticsVariant PLC.DefaultFun
      defaultBuiltinSemanticsVariant = def
  UPLC.optimizeProgramWithTrace opts defaultBuiltinSemanticsVariant renamed

execCertifier
  :: UPLC.OptimizerTrace UPLC.Name UPLC.DefaultUni UPLC.DefaultFun a
  -> CertName
  -> CertifierOutput
  -> [ ( Maybe
           (Cek.CekEvaluationException UPLC.NamedDeBruijn UPLC.DefaultUni UPLC.DefaultFun)
       , ExBudget
       )
     ]
  -> IO ()
execCertifier optimizerTrace cert out costs = do
  result <- runCertifier $ mkCertifier optimizerTrace cert out costs
  case result of
    Left err -> do
      putStrLn $ prettyCertifierError err
      case err of
        InvalidCertificate _ _ -> exitWith $ ExitFailure 1
        InvalidCompilerOutput -> exitWith $ ExitFailure 2
        ValidationError _ -> exitWith $ ExitFailure 3
    -- TODO: Only Right True is success
    Right _ -> pure ()

---------------- Load script arguments for evaluation ----------------

-- | Load hex-encoded args as @Program@s, one per `FilePath`.
loadProgramArgs :: [FilePath] -> IO [UplcTermNDB ()]
loadProgramArgs = traverse loadArg
  where
    loadArg path = do
      -- TODO: create a `readProgram` variant that returns `UplcProgDB` instead of `UplcProg`.
      prog <- readProgram Hex (FileInput path) :: IO (UplcProg SrcSpan)
      let term = void $ prog ^. UPLC.progTerm
      case runExcept @FreeVariableError $ UPLC.deBruijnTerm term of
        Left err -> fail $ "Error converting argument " <> path <> ": " <> show err
        Right t -> pure (void t)

-- | Load hex-encoded args as @Data@ objects, one per `FilePath`.
loadDataArgs :: [FilePath] -> IO [UplcTermNDB ()]
loadDataArgs = traverse loadArg
  where
    loadArg path = do
      hex <- T.readFile path
      case Base16.decode (T.encodeUtf8 (T.strip hex)) of
        Left err -> fail $ "Cannot hex-decode data argument " <> path <> ": " <> err
        Right bs ->
          case deserialiseOrFail @Data (BSL.fromStrict bs) of
            Left err -> fail $ "Cannot CBOR-decode data argument " <> path <> ": " <> show err
            Right d -> pure $ mkConstant () d

{-| Load hex-encoded args, which can be either @Program@s or @Data@ objects,
depending on `EvalArgKind`. One arg per `FilePath`. -}
loadArgs :: EvalArgKind -> [FilePath] -> IO [UplcTermNDB ()]
loadArgs kind = case kind of
  ArgProg -> loadProgramArgs
  ArgData -> loadDataArgs

{-| Load args from a dir.

It tries to load the first arg from the file named "0", second from "1", and so on,
until the file doesn't exist.

The args can be either @Program@s or @Data@ objects, depending on `EvalArgKind`. -}
loadArgsFromDir
  :: FilePath
  -> String
  -- ^ Validator title
  -> EvalArgKind
  -> IO (Maybe [UplcTermNDB ()])
loadArgsFromDir baseDir title argKind = do
  let dir = baseDir </> title
  paths <- collectArgFiles dir 0
  if null paths
    then pure Nothing
    else Just <$> loadArgs argKind paths
  where
    collectArgFiles dir n = do
      let path = dir </> show (n :: Int)
      exists <- doesFileExist path
      if exists
        then (path :) <$> collectArgFiles dir (n + 1)
        else pure []

-- | Returns `Nothing` if evaluation is not requested, otherwise `Just args`.
loadBlueprintArgs
  :: OptimiseEvalOpts
  -> String
  -> IO (Maybe [UplcTermNDB ()])
loadBlueprintArgs opts validatorName =
  case oeBlueprintArgsDir opts of
    Just dir -> do
      margs <- loadArgsFromDir dir validatorName (oeArgKind opts)
      case margs of
        Just args -> pure (Just args)
        Nothing | oeEval opts -> pure (Just [])
        Nothing -> pure Nothing
    Nothing ->
      -- Blueprint args dir not specified. Try loading args from files, and
      -- apply the same args to all validators in the blueprint.
      loadArgsIfEval opts

-- | Returns `Nothing` if evaluation is not requested, otherwise `Just args`.
loadArgsIfEval :: OptimiseEvalOpts -> IO (Maybe [UplcTermNDB ()])
loadArgsIfEval opts
  | not (oeEval opts) = pure Nothing
  | null (oeArgFiles opts) = pure (Just [])
  | otherwise = Just <$> loadArgs (oeArgKind opts) (oeArgFiles opts)

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
      evalCtx = mkDefaultEvalCtx semvar
      -- Evaluate the term the same way the 'time' subcommand (and production)
      -- does, erroring on an unexpected failure.
      cekEval = either (error . show) (const ()) . evaluateCekLikeInProd evalCtx
      -- readProgam throws away De Bruijn indices and returns an AST with Names;
      -- we have to put them back to get an AST with NamedDeBruijn names.
      term =
        fromRight (error "Unexpected open term in runBenchmark.")
          . runExcept @FreeVariableError
          $ UPLC.deBruijnTerm (UPLC._progTerm prog)
      -- Big names slow things down
      anonTerm = UPLC.termMapNames (\(PLC.NamedDeBruijn _ i) -> PLC.NamedDeBruijn "" i) term
      -- Big annotations slow things down.  Forcing this to NF here drives all
      -- the preparatory work (de Bruijn conversion, name anonymisation, 'void')
      -- to completion before benchmarking, so it isn't measured by Criterion.
      !unitAnnTerm = force (void anonTerm)
  benchmarkWith criterionConfig $! whnf cekEval unitAnnTerm

---------------- Evaluation ----------------

formatNs :: Integer -> String
formatNs ns
  | ns < 1000 = printf "%d ns" ns
  | ns < 1000000 = printf "%.3f \xb5s" (fromIntegral ns / 1000 :: Double)
  | ns < 1000000000 = printf "%.3f ms" (fromIntegral ns / 1000000 :: Double)
  | otherwise = printf "%.3f s" (fromIntegral ns / 1000000000 :: Double)

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
      SomeBudgetMode bm -> do
        report <- evaluate (Cek.runCek cekparams bm emitM term)
        let Cek.CekReport res budget logs = report
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

---------------- Timing ----------------

runTimeEval :: TimeEvalOptions -> IO ()
runTimeEval (TimeEvalOptions inp ifmt semvar n raw) = do
  prog <- readProgram ifmt inp
  let count = fromIntegral (max 1 n) :: Int
      term = void $ prog ^. UPLC.progTerm
      dbTerm =
        fromRight (error "time: term has free variables")
          . runExcept @FreeVariableError
          $ UPLC.deBruijnTerm term
  -- Fully evaluate the anonymised term to NF before timing.  This single
  -- 'force' drives all the preparatory work (the 'void', the de Bruijn
  -- conversion and the name anonymisation) to completion, since 'anonTerm'
  -- depends on all of it; doing it here keeps it out of the timed loop.
  anonTerm <-
    evaluate . force $
      UPLC.termMapNames (\(PLC.NamedDeBruijn _ i) -> PLC.NamedDeBruijn "" i) dbTerm
  let !evalCtx = mkDefaultEvalCtx semvar
  performGC
  -- Store the term in an IORef so GHC cannot CSE/share the result of
  -- evaluateCekLikeInProd across iterations.
  termRef <- newIORef anonTerm
  -- We measure CPU time (getCPUTime) rather than wall-clock time
  -- (getSystemTime): a CPU-time clock does not advance while the thread is
  -- descheduled, so the measurement is immune to contention from co-runners
  -- sharing the core.  In particular, running via 'cabal run' pins the
  -- long-lived cabal supervisor to the same core, and its periodic wake-ups
  -- would otherwise be charged to whichever evaluation happened to be in
  -- progress, inflating the reported time (especially for inputs that take
  -- longer to parse and so keep the process alive longer).
  let loop 0 !total = pure total
      loop k !total = do
        term' <- readIORef termRef
        t0 <- getCPUTime
        r <- evaluate (evaluateCekLikeInProd evalCtx term')
        t1 <- getCPUTime
        case r of
          Right _ -> loop (k - 1) (total + t1 - t0)
          Left e -> putStrLn (show e) >> exitFailure
  totalPs <- loop count 0
  -- getCPUTime returns picoseconds; convert the total to nanoseconds.
  let avgNs = totalPs `div` (1000 * fromIntegral count)
  putStrLn $
    if raw
      then show avgNs
      else
        (if count > 1 then "Average evaluation time (" ++ show count ++ " runs): " else "Evaluation time: ")
          ++ formatNs avgNs

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
    TimeEval opts -> runTimeEval opts
    Dbg opts -> runDbg opts
    Example opts -> runUplcPrintExample opts
    Optimise opts -> runOptimisations opts
    Print opts -> runPrint @UplcProg opts
    Convert opts -> runConvert @UplcProg opts
    DumpModel opts -> runDumpModel opts
    PrintBuiltinSignatures -> runPrintBuiltinSignatures
