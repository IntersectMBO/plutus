{-# LANGUAGE BangPatterns     #-}
{-# LANGUAGE LambdaCase       #-}
{-# LANGUAGE TypeApplications #-}

module Main (main) where

import PlutusCore qualified as PLC
import PlutusCore.Compiler.Erase qualified as PLC (eraseProgram)
import PlutusCore.Evaluation.Machine.Ck qualified as Ck
import PlutusCore.Evaluation.Machine.ExBudgetingDefaults qualified as PLC
import PlutusCore.Executable.Common
import PlutusCore.Executable.Parsers
import PlutusCore.Pretty qualified as PP

import Data.Maybe (fromJust)
import Data.Text.IO qualified as T
import PlutusPrelude

import Control.DeepSeq (rnf)
import Options.Applicative
import System.Exit (exitSuccess)

plcHelpText :: String
plcHelpText = helpText "Typed Plutus Core"

plcInfoCommand :: ParserInfo Command
plcInfoCommand = plutus plcHelpText

data TypecheckOptions = TypecheckOptions Input Format
data EvalOptions      = EvalOptions Input Format PrintMode TimingMode
data EraseOptions     = EraseOptions Input Format Output Format PrintMode


-- Main commands
data Command = Apply     ApplyOptions
             | Typecheck TypecheckOptions
             | Convert   ConvertOptions
             | Print     PrintOptions
             | Example   ExampleOptions
             | Erase     EraseOptions
             | Eval      EvalOptions
             | DumpModel
             | PrintBuiltinSignatures

---------------- Option parsers ----------------

typecheckOpts :: Parser TypecheckOptions
typecheckOpts = TypecheckOptions <$> input <*> inputformat

eraseOpts :: Parser EraseOptions
eraseOpts = EraseOptions <$> input <*> inputformat <*> output <*> outputformat <*> printmode

evalOpts :: Parser EvalOptions
evalOpts =
  EvalOptions <$> input <*> inputformat <*> printmode <*> timingmode

plutus ::
  -- | The @helpText@
  String ->
  ParserInfo Command
plutus langHelpText =
    info
      (plutusOpts <**> helper)
      (fullDesc <> header "Typed Plutus Core Tool" <> progDesc langHelpText)

plutusOpts :: Parser Command
plutusOpts = hsubparser (
       command "apply"
           (info (Apply <$> applyOpts)
            (progDesc $
            "Given a list of input scripts f g1 g2 ... gn, output a script consisting of "
              ++ "(... ((f g1) g2) ... gn); "
              ++ "for example, "
              ++ "'plc apply --if flat Validator.flat Datum.flat Redeemer.flat Context.flat"
              ++" --of flat -o Script.flat'"))
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
    <> command "typecheck"
           (info (Typecheck <$> typecheckOpts)
            (progDesc "Typecheck a typed Plutus Core program."))
    <> command "erase"
           (info (Erase <$> eraseOpts)
            (progDesc "Convert a typed Plutus Core program to an untyped one."))
    <> command "evaluate"
           (info (Eval <$> evalOpts)
            (progDesc "Evaluate a typed Plutus Core program using the CK machine."))
    <> command "dump-model"
           (info (pure DumpModel)
            (progDesc "Dump the cost model parameters"))
    <> command "print-builtin-signatures"
           (info (pure PrintBuiltinSignatures)
            (progDesc "Print the signatures of the built-in functions"))
  )

---------------- Script application ----------------

-- | Apply one script to a list of others.
runApply :: ApplyOptions -> IO ()
runApply (ApplyOptions inputfiles ifmt outp ofmt mode) = do
  scripts <- mapM ((getProgram ifmt ::  Input -> IO (PlcProg PLC.SrcSpan)) . FileInput) inputfiles
  let appliedScript =
        case map (\case p -> () <$ p) scripts of
          []          -> errorWithoutStackTrace "No input files"
          progAndargs -> foldl1 (fromJust .* PLC.applyProgram) progAndargs
  writeProgram outp ofmt mode appliedScript

---------------- Typechecking ----------------

runTypecheck :: TypecheckOptions -> IO ()
runTypecheck (TypecheckOptions inp fmt) = do
  prog <- getProgram fmt inp
  case PLC.runQuoteT $ do
    tcConfig <- PLC.getDefTypeCheckConfig ()
    PLC.inferTypeOfProgram tcConfig (void prog)
    of
      Left (e :: PLC.Error PLC.DefaultUni PLC.DefaultFun ()) ->
        errorWithoutStackTrace $ PP.displayPlcDef e
      Right ty                                               ->
        T.putStrLn (PP.displayPlcDef ty) >> exitSuccess

---------------- Evaluation ----------------

runEval :: EvalOptions -> IO ()
runEval (EvalOptions inp ifmt printMode timingMode) = do
  prog <- getProgram ifmt inp
  let evaluate = Ck.evaluateCkNoEmit PLC.defaultBuiltinsRuntime
      term = void $ prog ^. PLC.progTerm
      !_ = rnf term
      -- Force evaluation of body to ensure that we're not timing parsing/deserialisation.
      -- The parser apparently returns a fully-evaluated AST, but let's be on the safe side.
  case timingMode of
    NoTiming -> evaluate term & handleEResult printMode
    Timing n -> timeEval n evaluate term >>= handleTimingResults term

----------------- Print examples -----------------------

runPlcPrintExample ::
    ExampleOptions -> IO ()
runPlcPrintExample = runPrintExample getPlcExamples

---------------- Erasure ----------------

-- | Input a program, erase the types, then output it
runErase :: EraseOptions -> IO ()
runErase (EraseOptions inp ifmt outp ofmt mode) = do
  typedProg <- (getProgram ifmt inp :: IO (PlcProg PLC.SrcSpan))
  let untypedProg = () <$ PLC.eraseProgram typedProg
  case ofmt of
    Textual       -> writePrettyToFileOrStd outp mode untypedProg
    Flat flatMode -> writeFlat outp flatMode untypedProg

---------------- Driver ----------------

main :: IO ()
main = do
    options <- customExecParser (prefs showHelpOnEmpty) plcInfoCommand
    case options of
        Apply     opts         -> runApply        opts
        Typecheck opts         -> runTypecheck    opts
        Eval      opts         -> runEval         opts
        Example   opts         -> runPlcPrintExample opts
        Erase     opts         -> runErase        opts
        Print     opts         -> runPrint        opts
        Convert   opts         -> runConvert @PlcProg opts
        DumpModel              -> runDumpModel
        PrintBuiltinSignatures -> runPrintBuiltinSignatures
