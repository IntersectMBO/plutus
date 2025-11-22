{-# OPTIONS_GHC -Wno-name-shadowing #-}

{- Note [Profiling instructions]
Workflow for profiling evaluation time:
1. Compile your program with the Plutus Tx plugin option profile-all
2. Get the program you want to run, either by extracting it from the emulator logs,
or by using the Plutus Tx plugin option 'dump-uplc' if you have a self-contained program.
3. Run the dumped program with 'uplc --trace-mode LogsWithTimestamps -o logs'
4. Run 'cat logs | traceToStacks | flamegraph.pl > out.svg'
5. Open out.svg in your viewer of choice e.g. firefox.

You can also profile the abstract memory and budget units.
To do so, run 'uplc' with '--trace-mode LogsWithBudgets'.
This will give you CSV output with two numeric columns. By default 'traceToStacks'
will use the first numeric column (CPU), so will give you a CPU flamegraph, but you can
control this with the '--column' argument.
-}

-- | Executable for profiling. See Note [Profiling instructions]
module Main where

import Common
import Data.ByteString.Lazy qualified as BSL
import Data.List (intercalate)
import Options.Applicative

column :: Parser Int
column =
  option
    auto
    ( long "column"
        <> short 'c'
        <> metavar "COL"
        <> value 1
        <> showDefault
        <> help "Column to take profiling values from."
    )

data Input
  = FileInput FilePath
  | StdInput

fileInput :: Parser Input
fileInput =
  FileInput
    <$> strOption
      ( long "file"
          <> short 'f'
          <> metavar "FILENAME"
          <> help "Input file"
      )

input :: Parser Input
input = fileInput <|> pure StdInput

data Opts = Opts Input Int

opts :: ParserInfo Opts
opts =
  info
    ((Opts <$> input <*> column) <**> helper)
    (fullDesc <> progDesc "Turn PLC log output into flamegraph stacks output")

main :: IO ()
main = do
  Opts inp valIx <- execParser opts
  input <- case inp of
    FileInput fp -> BSL.readFile fp
    StdInput -> BSL.getContents
  let processed = processLog valIx input
  putStrLn (intercalate "\n" (map show processed))
