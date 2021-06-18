{-# LANGUAGE BangPatterns      #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications  #-}

module Main (main) where


import           Common
import qualified PlutusCore          as PLC


import           Options.Applicative

uplcHelpText :: String
uplcHelpText = helpText "Untyped Plutus Core"

uplcInfoCommand :: ParserInfo Command
uplcInfoCommand = plutus "Untyped Plutus Core Tool" uplcHelpText

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
        Apply     _opts -> errorWithoutStackTrace "Not supported in Untyped plutus core." --runApply        opts
        Typecheck opts  -> runTypecheck    opts
        Eval      opts  -> runEval         opts
        Example   opts  -> runPrintExample opts
        Erase     opts  -> runErase        opts
        Print     opts  -> runPrint        opts
        Convert   opts  -> runConvert      opts
