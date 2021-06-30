{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE LambdaCase   #-}
module Main (main) where

import           Common
import qualified PlutusCore                       as PLC
import qualified PlutusCore.Evaluation.Machine.Ck as Ck
import qualified PlutusCore.Pretty                as PP

import qualified UntypedPlutusCore                as UPLC (eraseProgram)

import           Data.Function                    ((&))
import           Data.Functor                     (void)
import qualified Data.Text.IO                     as T

import           Control.DeepSeq                  (rnf)
import           Options.Applicative              (ParserInfo, customExecParser, prefs, showHelpOnEmpty)
import           System.Exit                      (exitSuccess)

plcHelpText :: String
plcHelpText = helpText "Typed Plutus Core"

plcInfoCommand :: ParserInfo Command
plcInfoCommand = plutus "Typed Plutus Core Tool" plcHelpText

---------------- Script application ----------------

-- | Apply one script to a list of others.
runApply :: ApplyOptions -> IO ()
runApply (ApplyOptions inputfiles ifmt outp ofmt mode) = do
  scripts <- mapM ((getProgram ifmt ::  Input -> IO (PlcProg PLC.AlexPosn)) . FileInput) inputfiles
  let appliedScript =
        case map (\case p -> () <$ p) scripts of
          []          -> errorWithoutStackTrace "No input files"
          progAndargs -> foldl1 PLC.applyProgram progAndargs
  writeProgram outp ofmt mode appliedScript

---------------- Typechecking ----------------

runTypecheck :: TypecheckOptions -> IO ()
runTypecheck (TypecheckOptions inp fmt) = do
  prog <- getProgram fmt inp
  case PLC.runQuoteT $ do
    tcConfig <- PLC.getDefTypeCheckConfig ()
    PLC.typecheckPipeline tcConfig (void prog)
    of
      Left (e :: PLC.Error PLC.DefaultUni PLC.DefaultFun ()) ->
        errorWithoutStackTrace $ PP.displayPlcDef e
      Right ty                                               ->
        T.putStrLn (PP.displayPlcDef ty) >> exitSuccess

---------------- Evaluation ----------------

runEval :: EvalOptions -> IO ()
runEval (EvalOptions inp ifmt evalMode printMode budgetMode timingMode _) =
  case evalMode of
      CEK -> errorWithoutStackTrace "There is no CEK machine for Typed Plutus Core"
      CK  -> do
              let !_ = case budgetMode of
                          Silent    -> ()
                          Verbose _ -> errorWithoutStackTrace "There is no budgeting for typed Plutus Core"
              prog <- getProgram ifmt inp
              let evaluate = Ck.evaluateCkNoEmit PLC.defaultBuiltinsRuntime
                  term = void . PLC.toTerm $ prog
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
  typedProg <- (getProgram ifmt inp :: IO (PlcProg PLC.AlexPosn))
  let untypedProg = () <$ UPLC.eraseProgram typedProg
  case ofmt of
    Textual       -> writeToFileOrStd outp mode untypedProg
    Cbor cborMode -> writeCBOR outp cborMode untypedProg
    Flat flatMode -> writeFlat outp flatMode untypedProg



---------------- Parse and print a PLC source file ----------------

runPrint :: PrintOptions -> IO ()
runPrint (PrintOptions inp mode) =
    (parseInput inp :: IO (PlcProg PLC.AlexPosn) ) >>= print . getPrintMethod mode

---------------- Conversions ----------------

-- | Convert between textual and CBOR representations.  This subsumes the
-- `print` command: for example, `plc convert -i prog.plc --typed --fmt Readable`
-- will read a typed plc file and print it in the Readable format.  Having
-- the separate `print` option may be more user-friendly though.
runConvert :: ConvertOptions -> IO ()
runConvert (ConvertOptions inp ifmt outp ofmt mode) = do
    program <- (getProgram ifmt inp :: IO (PlcProg PLC.AlexPosn))
    writeProgram outp ofmt mode program

---------------- Driver ----------------
-- TODO will be done via type instance?
main :: IO ()
main = do
    options <- customExecParser (prefs showHelpOnEmpty) plcInfoCommand
    case options of
        Apply     opts -> runApply        opts
        Typecheck opts -> runTypecheck    opts
        Eval      opts -> runEval         opts
        Example   opts -> runPlcPrintExample opts
        Erase     opts -> runErase        opts
        Print     opts -> runPrint        opts
        Convert   opts -> runConvert      opts
