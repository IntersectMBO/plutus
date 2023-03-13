module Main where

import CreateBuiltinCostModel (createBuiltinCostModel)

import Data.Aeson.Encode.Pretty
import Data.ByteString.Lazy qualified as BSL (ByteString, putStr, writeFile)
import Options.Applicative
import System.Directory
import System.Exit
import System.IO (hPutStrLn, stderr)

{- | This takes a CSV file of benchmark results for built-in functions, runs the R
   code in `models.R` to construct costing functions based on the benchmark
   results, and then produces JSON output containing the types and coefficients
   of the costing functions. For best results, run this in
   `plutus-core/cost-model/data` to make `models.R` easy to find; if that's
   inconvenient for some reason, use the `-m` option to provide a path to
   `models.R`.

   See also CostModelGeneration.md.
-}

-- | The file containing the benchmark results, 'benching.csv' by default.  We
-- can't read this from stdin because we have to supply the filename to inline R
-- in a splice.
data BenchmarkFile = BenchmarkFile FilePath

defaultBenchmarkFile :: BenchmarkFile
defaultBenchmarkFile = BenchmarkFile "benching.csv"

-- | The file containing the R modelling code, `models.R` by default.
-- This is a bit tricky because it's in a fixed location, so it could be difficult
-- to find.  See the warning message later.
data RFile = RFile FilePath

defaultRFile :: RFile
defaultRFile = RFile "models.R"

-- | Where to write the JSON output, stdout by default
data Output = NamedOutput FilePath | StdOutput


---------------- Option parsers ----------------

benchmarkFile :: Parser BenchmarkFile
benchmarkFile = namedBenchmarkFile <|> pure defaultBenchmarkFile

-- | Parser for an input stream. If none is specified, default to stdin:
-- this makes use in pipelines easier
namedBenchmarkFile :: Parser BenchmarkFile
namedBenchmarkFile = BenchmarkFile <$> strOption
  (  long "csv"
  <> metavar "FILENAME"
  <> help "CSV file containing built-in function benchmark results")


rFile :: Parser RFile
rFile =  namedRFile <|> pure defaultRFile

namedRFile :: Parser RFile
namedRFile  = RFile <$> strOption
  (  long "models"
  <> short 'm'
  <> metavar "FILENAME"
  <> help "The file containing the R modelling code" )


-- | Parser for an output stream. If none is specified, default to stdout:
-- this makes use in pipelines easier
output :: Parser Output
output = fileOutput <|> stdOutput <|> pure StdOutput

fileOutput :: Parser Output
fileOutput = NamedOutput <$> strOption
  (  long "output"
  <> short 'o'
  <> metavar "FILENAME"
  <> help "Output file" )

stdOutput :: Parser Output
stdOutput = flag' StdOutput
  (  long "stdout"
  <> help "Write to stdout (default)" )

inputsAndOutput :: Parser (BenchmarkFile, RFile, Output)
inputsAndOutput = (,,) <$> benchmarkFile  <*> rFile <*> output

arguments :: ParserInfo (BenchmarkFile, RFile, Output)
arguments = info
        (inputsAndOutput <**> helper)
        (fullDesc
         <> header "Plutus Core cost model creation tool"
         <> progDesc
                (  "Creates a JSON description of Plutus Core cost model "
                ++ "for built-in functions from a set of benchmark results "
                ++ "produced by cost-model-budgeting-bench")
        )


---------------- Checking files and processing input/output ----------------

checkInputFile :: FilePath -> String -> String -> IO ()
checkInputFile file filespec advice = do
  let putStrLnErr = hPutStrLn stderr
  exists <- doesFileExist file
  if not exists
  then do
    putStrLnErr ""
    putStrLnErr $ "ERROR: Cannot open " ++ filespec ++ " " ++ file
    putStrLnErr advice
    exitFailure
  else do
    perms <- getPermissions file
    if not $ readable perms
    then do
      putStrLnErr ""
      putStrLnErr $ "ERROR: cannot read " ++ filespec ++ " "  ++ file
      putStrLnErr advice
      exitFailure
    else pure ()

checkRFile :: FilePath -> IO ()
checkRFile file =
  let advice = "The default R model file is models.R in plutus-core/cost-model/data;\n"
               ++ "either run this program in that directory or supply the path to a\n"
               ++ "suitable R file with -m."
  in checkInputFile file "R model file" advice

checkBenchmarkFile :: FilePath -> IO ()
checkBenchmarkFile file =
  let advice = "Supply the path to a suitable benchmark results file with --csv.\n"
               ++ "The default results file is plutus-core/cost-model/data/benching.csv."
  in checkInputFile file "benchmark results file" advice


writeOutput ::
  Output -> BSL.ByteString -> IO ()
writeOutput outp v = do
  case outp of
        NamedOutput file -> BSL.writeFile file v
        StdOutput        -> BSL.putStr v

main :: IO ()
main = do
  (BenchmarkFile bmfile, RFile rfile, out) <- execParser arguments
  checkBenchmarkFile bmfile
  checkRFile rfile
  model <- createBuiltinCostModel bmfile rfile
  writeOutput out $ encodePretty' (defConfig { confCompare = \_ _-> EQ }) model
