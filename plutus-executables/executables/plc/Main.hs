{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeApplications #-}

module Main (main) where

import Data.Version.Extras (gitAwareVersionInfo)
import Paths_plutus_executables qualified as Paths
import PlutusCore qualified as PLC
import PlutusCore.Compiler.Erase qualified as PLC (eraseProgram)
import PlutusCore.Data
import PlutusCore.Default (BuiltinSemanticsVariant (..))
import PlutusCore.Evaluation.Machine.Ck qualified as Ck
import PlutusCore.Evaluation.Machine.ExBudgetingDefaults qualified as PLC
import PlutusCore.Executable.AstIO (toDeBruijnTermPLC, toDeBruijnTypePLC)
import PlutusCore.Executable.Common
import PlutusCore.Executable.Parsers
import PlutusCore.MkPlc (mkConstant)
import PlutusCore.Pretty qualified as PP
import PlutusPrelude

import Control.Monad.Except
import Data.ByteString.Lazy qualified as BSL (readFile)
import Options.Applicative
import PlutusCore.Flat (unflat)
import System.Exit (exitFailure)
import System.IO (hPrint, stderr)

plcHelpText :: String
plcHelpText = helpText "Typed Plutus Core"

plcInfoCommand :: ParserInfo Command
plcInfoCommand = plutus plcHelpText

data TypecheckOptions = TypecheckOptions Input Format Output PrintMode NameFormat

data EvalOptions
  = EvalOptions
      Input
      Format
      Output
      PrintMode
      NameFormat
      (BuiltinSemanticsVariant PLC.DefaultFun)

data EraseOptions = EraseOptions Input Format Output Format PrintMode

-- Main commands
data Command
  = Apply ApplyOptions
  | ApplyToData ApplyOptions
  | Typecheck TypecheckOptions
  | Optimise OptimiseOptions
  | Convert ConvertOptions
  | Print PrintOptions
  | Example ExampleOptions
  | Erase EraseOptions
  | Eval EvalOptions
  | DumpModel (BuiltinSemanticsVariant PLC.DefaultFun)
  | PrintBuiltinSignatures

---------------- Option parsers ----------------

typecheckOpts :: Parser TypecheckOptions
typecheckOpts = TypecheckOptions <$> input <*> inputformat <*> output <*> printmode <*> nameformat

eraseOpts :: Parser EraseOptions
eraseOpts = EraseOptions <$> input <*> inputformat <*> output <*> outputformat <*> printmode

evalOpts :: Parser EvalOptions
evalOpts =
  EvalOptions
    <$> input
    <*> inputformat
    <*> output
    <*> printmode
    <*> nameformat
    <*> builtinSemanticsVariant

plutus
  :: String
  -- ^ The @helpText@
  -> ParserInfo Command
plutus langHelpText =
  info
    (plutusOpts <**> versioner <**> helper)
    (fullDesc <> header "Typed Plutus Core Tool" <> progDesc langHelpText)

plutusOpts :: Parser Command
plutusOpts =
  hsubparser $
    command
      "apply"
      ( info
          (Apply <$> applyOpts)
          ( progDesc $
              "Given a list of input files f g1 g2 ... gn "
                <> "containing Typed Plutus Core scripts, "
                <> "output a script consisting of (... ((f g1) g2) ... gn); "
                <> "for example, 'plc apply --if flat Validator.flat "
                <> "Datum.flat Redeemer.flat Context.flat --of flat -o Script.flat'."
          )
      )
      <> command
        "apply-to-data"
        ( info
            (ApplyToData <$> applyOpts)
            ( progDesc $
                "Given a list f d1 d2 ... dn where f is a "
                  <> "Typed Plutus Core script and d1,...,dn are files "
                  <> "containing flat-encoded data ojbects, output a script "
                  <> "consisting of f applied to the data objects; "
                  <> "for example, 'plc apply-to-data --if "
                  <> "flat Validator.flat Datum.flat Redeemer.flat Context.flat "
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
            (progDesc "Convert a program between various formats")
        )
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
        "typecheck"
        ( info
            (Typecheck <$> typecheckOpts)
            (progDesc "Typecheck a typed Plutus Core program.")
        )
      <> command
        "optimise"
        ( optimise $
            "Run the PLC optimisation pipeline on the input.  "
              ++ "At present there are no PLC optimisations."
        )
      <> command "optimize" (optimise "Same as 'optimise'.")
      <> command
        "erase"
        ( info
            (Erase <$> eraseOpts)
            (progDesc "Convert a typed Plutus Core program to an untyped one.")
        )
      <> command
        "evaluate"
        ( info
            (Eval <$> evalOpts)
            (progDesc "Evaluate a typed Plutus Core program using the CK machine.")
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

---------------- Script application ----------------

{-| Apply one script to a list of others and output the result.  All of the
scripts must be PLC.Program objects. -}
runApply :: ApplyOptions -> IO ()
runApply (ApplyOptions inputfiles ifmt outp ofmt mode) = do
  scripts <- mapM ((readProgram ifmt :: Input -> IO (PlcProg PLC.SrcSpan)) . FileInput) inputfiles
  let appliedScript =
        case map (\case p -> () <$ p) scripts of
          [] -> errorWithoutStackTrace "No input files"
          progAndargs ->
            foldl1 (unsafeFromRight .* PLC.applyProgram) progAndargs
  writeProgram outp ofmt mode appliedScript

{-| Apply a PLC program to script to a list of flat-encoded Data objects and
output the result. -}
runApplyToData :: ApplyOptions -> IO ()
runApplyToData (ApplyOptions inputfiles ifmt outp ofmt mode) = do
  case inputfiles of
    [] -> errorWithoutStackTrace "No input files"
    p : ds -> do
      prog@(PLC.Program _ version _) :: PlcProg PLC.SrcSpan <- readProgram ifmt (FileInput p)
      args <- mapM (getDataObject version) ds
      let prog' = () <$ prog
          appliedScript = foldl1 (unsafeFromRight .* PLC.applyProgram) (prog' : args)
      writeProgram outp ofmt mode appliedScript
      where
        getDataObject :: PLC.Version -> FilePath -> IO (PlcProg ())
        getDataObject ver path = do
          bs <- BSL.readFile path
          case unflat bs of
            Left err -> fail ("Error reading " ++ show path ++ ": " ++ show err)
            Right (d :: Data) ->
              pure $ PLC.Program () ver $ mkConstant () d

---------------- Typechecking ----------------

runTypecheck :: TypecheckOptions -> IO ()
runTypecheck (TypecheckOptions inp fmt outp printMode nameFormat) = do
  prog <- readProgram fmt inp
  case PLC.runQuoteT $ modifyError PLC.TypeErrorE $ do
    tcConfig <- PLC.getDefTypeCheckConfig ()
    PLC.inferTypeOfProgram tcConfig (void prog) of
    Left (e :: PLC.Error PLC.DefaultUni PLC.DefaultFun ()) ->
      errorWithoutStackTrace $ PP.displayPlc e
    Right (PLC.Normalized ty) ->
      case nameFormat of
        IdNames -> writeToOutput outp $ prettyPrintByMode printMode ty
        DeBruijnNames ->
          writeToOutput outp $ prettyPrintByMode printMode $ toDeBruijnTypePLC ty

---------------- Optimisation ----------------

runOptimisations :: OptimiseOptions -> IO ()
runOptimisations (OptimiseOptions inp ifmt outp ofmt mode _) = do
  prog <- readProgram ifmt inp :: IO (PlcProg PLC.SrcSpan)
  let optimised = prog -- No PLC optimisations at present!
  writeProgram outp ofmt mode optimised

---------------- Evaluation ----------------

runEval :: EvalOptions -> IO ()
runEval (EvalOptions inp ifmt outp printMode nameFormat semvar) = do
  prog <- readProgram ifmt inp
  let evaluate = Ck.evaluateCkNoEmit (PLC.defaultBuiltinsRuntimeForSemanticsVariant semvar) def
      term = void $ prog ^. PLC.progTerm
  case evaluate term of
    Right v ->
      case nameFormat of
        IdNames -> writeToOutput outp (prettyPrintByMode printMode v)
        DeBruijnNames ->
          writeToOutput outp (prettyPrintByMode printMode $ toDeBruijnTermPLC v)
    Left err -> hPrint stderr err *> exitFailure

----------------- Print examples -----------------------

runPlcPrintExample :: ExampleOptions -> IO ()
runPlcPrintExample = runPrintExample getPlcExamples

---------------- Erasure ----------------

-- | Input a program, erase the types, then output it
runErase :: EraseOptions -> IO ()
runErase (EraseOptions inp ifmt outp ofmt mode) = do
  typedProg <- (readProgram ifmt inp :: IO (PlcProg PLC.SrcSpan))
  let untypedProg = () <$ PLC.eraseProgram typedProg
  case ofmt of
    Textual -> writePrettyToOutput outp mode untypedProg
    Flat flatMode -> writeFlat outp flatMode untypedProg

---------------- Version ----------------

versioner :: Parser (a -> a)
versioner = simpleVersioner (gitAwareVersionInfo Paths.version)

---------------- Driver ----------------

main :: IO ()
main = do
  options <- customExecParser (prefs showHelpOnEmpty) plcInfoCommand
  case options of
    Apply opts -> runApply opts
    ApplyToData opts -> runApplyToData opts
    Typecheck opts -> runTypecheck opts
    Optimise opts -> runOptimisations opts
    Eval opts -> runEval opts
    Example opts -> runPlcPrintExample opts
    Erase opts -> runErase opts
    Print opts -> runPrint @PlcProg opts
    Convert opts -> runConvert @PlcProg opts
    DumpModel opts -> runDumpModel opts
    PrintBuiltinSignatures -> runPrintBuiltinSignatures
