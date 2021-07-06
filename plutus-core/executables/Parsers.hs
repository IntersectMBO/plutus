{-# LANGUAGE LambdaCase #-}

-- | Common option parsers for executables

module Parsers where

import           Common

import           PlutusCore.Evaluation.Machine.ExBudget   (ExBudget (..), ExRestrictingBudget (..))
import           PlutusCore.Evaluation.Machine.ExMemory   (ExCPU (..), ExMemory (..))

import qualified UntypedPlutusCore.Evaluation.Machine.Cek as Cek

import           Data.Foldable                            (asum)
import           Data.List.Split                          (splitOn)

import           Options.Applicative

import           Text.Read                                (readMaybe)

-- | Parser for an input stream. If none is specified, default to stdin: this makes use in pipelines easier
input :: Parser Input
input = fileInput <|> stdInput <|> pure StdInput

fileInput :: Parser Input
fileInput = FileInput <$> strOption
  (  long "input"
  <> short 'i'
  <> metavar "FILENAME"
  <> help "Input file" )

stdInput :: Parser Input
stdInput = flag' StdInput
  (  long "stdin"
  <> help "Read from stdin (default)" )

-- | Parser for an output stream. If none is specified, default to stdout: this makes use in pipelines easier
output :: Parser Output
output = fileOutput <|> stdOutput <|> pure StdOutput

fileOutput :: Parser Output
fileOutput = FileOutput <$> strOption
  (  long "output"
  <> short 'o'
  <> metavar "FILENAME"
  <> help "Output file" )

stdOutput :: Parser Output
stdOutput = flag' StdOutput
  (  long "stdout"
  <> help "Write to stdout (default)" )

formatHelp :: String
formatHelp =
  "plc, cbor (de Bruijn indices), cbor-named (names), flat (de Bruijn indices), or flat-named (names)"

formatReader :: String -> Maybe Format
formatReader =
    \case
         "textual"       -> Just Textual
         "cbor-named"    -> Just (Cbor Named)
         "cbor"          -> Just (Cbor DeBruijn)
         "cbor-deBruijn" -> Just (Cbor DeBruijn)
         "flat-named"    -> Just (Flat Named)
         "flat"          -> Just (Flat DeBruijn)
         "flat-deBruijn" -> Just (Flat DeBruijn)
         _               -> Nothing

inputformat :: Parser Format
inputformat = option (maybeReader formatReader)
  (  long "if"
  <> long "input-format"
  <> metavar "FORMAT"
  <> value Textual
  <> showDefault
  <> help ("Input format: " ++ formatHelp))

outputformat :: Parser Format
outputformat = option (maybeReader formatReader)
  (  long "of"
  <> long "output-format"
  <> metavar "FORMAT"
  <> value Textual
  <> showDefault
  <> help ("Output format: " ++ formatHelp))

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
restrictingbudgetEnormous = flag' (Verbose Cek.restrictingEnormous)
                            (  long "restricting-enormous"
                            <> short 'r'
                            <> help "Run the machine in restricting mode with an enormous budget" )

restrictingbudget :: Parser BudgetMode
restrictingbudget = Verbose . Cek.restricting . ExRestrictingBudget
                    <$> option exbudgetReader
                            (  long "restricting"
                            <> short 'R'
                            <> metavar "ExCPU:ExMemory"
                            <> help "Run the machine in restricting mode with the given limits" )

countingbudget :: Parser BudgetMode
countingbudget = flag' (Verbose Cek.counting)
                 (  long "counting"
                 <> short 'c'
                 <> help "Run machine in counting mode and report results" )

tallyingbudget :: Parser BudgetMode
tallyingbudget = flag' (Verbose Cek.tallying)
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

-- -x -> run 100 times and print the mean time
timing1 :: Parser TimingMode
timing1 = flag NoTiming (Timing 100)
  (  short 'x'
  <> help "Report mean execution time of program over 100 repetitions"
  )

-- -X N -> run N times and print the mean time
timing2 :: Parser TimingMode
timing2 = Timing <$> option auto
  (  long "time-execution"
  <> short 'X'
  <> metavar "N"
  <> help "Report mean execution time of program over N repetitions. Use a large value of N if possible to get accurate results."
  )

-- We really do need two separate parsers here.
-- See https://github.com/pcapriotti/optparse-applicative/issues/194#issuecomment-205103230
timingmode :: Parser TimingMode
timingmode = timing1 <|> timing2

files :: Parser Files
files = some (argument str (metavar "[FILES...]"))

applyOpts :: Parser ApplyOptions
applyOpts = ApplyOptions <$>  files <*> inputformat <*> output <*> outputformat <*> printmode

printmode :: Parser PrintMode
printmode = option auto
  (  long "print-mode"
  <> metavar "MODE"
  <> value Classic
  <> showDefault
  <> help ("Print mode for plc output (ignored elsewhere): Classic -> plcPrettyClassicDef, Debug -> plcPrettyClassicDebug, "
        ++ "Readable -> prettyPlcReadableDef, ReadableDebug -> prettyPlcReadableDebug" ))

printOpts :: Parser PrintOptions
printOpts = PrintOptions <$> input <*> printmode

convertOpts :: Parser ConvertOptions
convertOpts = ConvertOptions <$> input <*> inputformat <*> output <*> outputformat <*> printmode

exampleMode :: Parser ExampleMode
exampleMode = exampleAvailable <|> exampleSingle

exampleAvailable :: Parser ExampleMode
exampleAvailable = flag' ExampleAvailable
  (  long "available"
  <> short 'a'
  <> help "Show available examples")

exampleName :: Parser ExampleName
exampleName = strOption
  (  long "single"
  <> metavar "NAME"
  <> short 's'
  <> help "Show a single example")

exampleSingle :: Parser ExampleMode
exampleSingle = ExampleSingle <$> exampleName

exampleOpts :: Parser ExampleOptions
exampleOpts = ExampleOptions <$> exampleMode
