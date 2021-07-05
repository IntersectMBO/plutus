{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE LambdaCase   #-}

module Main (main) where


import           Common
import qualified PlutusCore                               as PLC

import qualified UntypedPlutusCore                        as UPLC
import qualified UntypedPlutusCore.Evaluation.Machine.Cek as Cek

import           Data.Function                            ((&))
import           Data.Functor                             (void)
import           Data.List                                (nub)

import           Control.DeepSeq                          (rnf)
import           Options.Applicative
import           System.Exit                              (exitFailure, exitSuccess)

uplcHelpText :: String
uplcHelpText = helpText "Untyped Plutus Core"

uplcInfoCommand :: ParserInfo Command
uplcInfoCommand = plutus uplcHelpText

data EvalOptions      = EvalOptions Input Format PrintMode BudgetMode TimingMode CekModel


-- Main commands
data Command = Apply     ApplyOptions
             | Convert   ConvertOptions
             | Print     PrintOptions
             | Example   ExampleOptions
             | Eval      EvalOptions

---------------- Option parsers ----------------


cekmodel :: Parser CekModel
cekmodel = flag Default Unit
           (  short '1'
           <> long "unit-cek-model"
           <> help "Use unit AST node costs for CEK cost model (tallying mode only)"
           )

evalOpts :: Parser EvalOptions
evalOpts =
  EvalOptions <$> input <*> inputformat <*> printmode <*> budgetmode <*> timingmode <*> cekmodel

plutus ::
  -- | The @helpfText@
  String ->
  ParserInfo Command
plutus langHelpText =
    info
      (plutusOpts <**> helper)
      (fullDesc <> header "Untyped Plutus Core Tool" <> progDesc langHelpText)

plutusOpts :: Parser Command
plutusOpts = hsubparser (
       command "apply"
           (info (Apply <$> applyOpts)
            (progDesc $ "Given a list of input scripts f g1 g2 ... gn, output a script consisting of (... ((f g1) g2) ... gn); "
            ++ "for example, 'plc apply --if cbor Validator.cbor Datum.cbor Redeemer.cbor Context.cbor --of cbor -o Script.cbor'"))
    <> command "print"
           (info (Print <$> printOpts)
            (progDesc "Parse a program then prettyprint it."))
    <> command "convert"
           (info (Convert <$> convertOpts)
            (progDesc "Convert a program between various formats"))
    <> command "example"
           (info (Example <$> exampleOpts)
            (progDesc $ "Show a program example. "
                     ++ "Usage: first request the list of available examples (optional step), "
                     ++ "then request a particular example by the name of a term. "
                     ++ "Note that evaluating a generated example may result in 'Failure'."))
    <> command "evaluate"
           (info (Eval <$> evalOpts)
            (progDesc "Evaluate a Plutus Core program."))
  )


---------------- Script application ----------------

-- | Apply one script to a list of others.
runApply :: ApplyOptions -> IO ()
runApply (ApplyOptions inputfiles ifmt outp ofmt mode) = do
  scripts <- mapM ((getProgram ifmt ::  Input -> IO (UplcProg PLC.AlexPosn)) . FileInput) inputfiles
  let appliedScript =
        case map (\case p -> () <$ p) scripts of
          []          -> errorWithoutStackTrace "No input files"
          progAndargs -> foldl1 UPLC.applyProgram progAndargs
  writeProgram outp ofmt mode appliedScript


runEval :: EvalOptions -> IO ()
runEval (EvalOptions inp ifmt printMode budgetMode timingMode cekModel) = do
    prog <- getProgram ifmt inp
    let term = void . UPLC.toTerm $ prog
        !_ = rnf term
        cekparams = case cekModel of
                    Default -> PLC.defaultCekParameters  -- AST nodes are charged according to the default cost model
                    Unit    -> PLC.unitCekParameters     -- AST nodes are charged one unit each, so we can see how many times each node
                                                        -- type is encountered.  This is useful for calibrating the budgeting code.
    case budgetMode of
        Silent -> do
            let evaluate = Cek.evaluateCekNoEmit cekparams
            case timingMode of
                NoTiming -> evaluate term & handleEResult printMode
                Timing n -> timeEval n evaluate term >>= handleTimingResults term
        Verbose bm -> do
            let evaluate = Cek.runCekNoEmit cekparams bm
            case timingMode of
                NoTiming -> do
                        let (result, budget) = evaluate term
                        printBudgetState term cekModel budget
                        handleResultSilently result  -- We just want to see the budget information
                Timing n -> timeEval n evaluate term >>= handleTimingResultsWithBudget term
    where
        handleResultSilently =
            \case
                Right _  -> exitSuccess
                Left err -> print err >> exitFailure
        handleTimingResultsWithBudget term results =
            case nub results of
            [(Right _, budget)] -> do
                putStrLn ""
                printBudgetState term cekModel budget
                exitSuccess
            [(Left err,   budget)] -> do
                putStrLn ""
                print err
                printBudgetState term cekModel budget
                exitFailure
            _                                   -> error "Timing evaluations returned inconsistent results"

----------------- Print examples -----------------------
runUplcPrintExample ::
    ExampleOptions -> IO ()
runUplcPrintExample = runPrintExample getUplcExamples

---------------- Parse and print a UPLC source file ----------------

runPrint :: PrintOptions -> IO ()
runPrint (PrintOptions inp mode) =
    (parseInput inp :: IO (UplcProg PLC.AlexPosn)) >>= print . getPrintMethod mode

---------------- Conversions ----------------

-- | Convert between textual and CBOR representations.  This subsumes the
-- `print` command: for example, `plc convert -i prog.plc --typed --fmt Readable`
-- will read a typed plc file and print it in the Readable format.  Having
-- the separate `print` option may be more user-friendly though.
runConvert :: ConvertOptions -> IO ()
runConvert (ConvertOptions inp ifmt outp ofmt mode) = do
    program <- (getProgram ifmt inp :: IO (UplcProg PLC.AlexPosn))
    writeProgram outp ofmt mode program


main :: IO ()
main = do
    options <- customExecParser (prefs showHelpOnEmpty) uplcInfoCommand
    case options of
        Apply     opts -> runApply        opts
        Eval      opts -> runEval         opts
        Example   opts -> runUplcPrintExample opts
        Print     opts -> runPrint        opts
        Convert   opts -> runConvert      opts
