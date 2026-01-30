{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeApplications #-}

module Main (main) where

import Control.Concurrent (threadDelay)
import Control.DeepSeq (NFData, force)
import Control.Exception (SomeException, catch, evaluate, try)
import Control.Monad (foldM, replicateM, replicateM_, unless)
import Criterion.Measurement (getTime, initializeTime)
import Data.Aeson (ToJSON (..), (.=))
import Data.Aeson qualified as Aeson
import Data.ByteString.Lazy qualified as BSL
import Data.List (isPrefixOf, isSuffixOf)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.SatInt (fromSatInt)
import Data.Text (Text)
import Data.Text qualified as T
import Data.Text.IO qualified as TIO
import Data.UUID (UUID)
import Data.UUID qualified as UUID
import Data.Word (Word64)
import GHC.Generics (Generic)
import Main.Utf8 (withUtf8)
import Options.Applicative
import PlutusCore qualified as PLC
import PlutusCore.Evaluation.Machine.ExBudget (ExBudget (..))
import PlutusCore.Evaluation.Machine.ExBudgetingDefaults qualified as PLC
import PlutusCore.Evaluation.Machine.ExMemory (ExCPU (..), ExMemory (..))
import PlutusCore.Quote (runQuoteT)
import PlutusPrelude (void)
import System.Directory
import System.Exit (exitFailure)
import System.FilePath (takeBaseName, takeExtension, (</>))
import System.IO (BufferMode (LineBuffering), hPutStrLn, hSetBuffering, stderr)
import UntypedPlutusCore qualified as UPLC
import UntypedPlutusCore.Evaluation.Machine.Cek qualified as Cek
import UntypedPlutusCore.Parser qualified as UPLC.Parser

-- | Configuration for the evaluator service
data Config = Config
  { cfgInputDir :: FilePath
  , cfgOutputDir :: FilePath
  , cfgPollInterval :: Int -- milliseconds
  }
  deriving stock (Show)

-- | Command line options parser
configParser :: Parser Config
configParser =
  Config
    <$> strOption
      ( long "input-dir"
          <> short 'i'
          <> metavar "DIR"
          <> value "/benchmarking/input"
          <> help "Input directory to watch for UPLC programs"
      )
    <*> strOption
      ( long "output-dir"
          <> short 'o'
          <> metavar "DIR"
          <> value "/benchmarking/output"
          <> help "Output directory for evaluation results"
      )
    <*> option
      auto
      ( long "poll-interval"
          <> short 'p'
          <> metavar "MS"
          <> value 1000
          <> help "Polling interval in milliseconds (default: 1000)"
      )

-- | Timing sample for a single evaluation run
newtype TimingSample = TimingSample {tsCpuTimeNs :: Word64}
  deriving stock (Generic, Show)

instance ToJSON TimingSample where
  toJSON TimingSample {..} =
    Aeson.object
      [ "cpu_time_ns" .= tsCpuTimeNs
      ]

-- | Successful evaluation result with deterministic budget at top level
data EvalResult = EvalResult
  { erProgramId :: Text
  , erStatus :: Text
  , erCpuBudget :: Integer
  , erMemoryBudget :: Integer
  , erMemoryBytes :: Integer
  , erTimingSamples :: [TimingSample]
  }
  deriving stock (Generic, Show)

instance ToJSON EvalResult where
  toJSON EvalResult {..} =
    Aeson.object
      [ "program_id" .= erProgramId
      , "status" .= erStatus
      , "cpu_budget" .= erCpuBudget
      , "memory_budget" .= erMemoryBudget
      , "memory_bytes" .= erMemoryBytes
      , "timing_samples" .= erTimingSamples
      ]

-- | Error result
data EvalError = EvalError
  { eeProgramId :: Text
  , eeStatus :: Text
  , eeErrorType :: Text
  , eeErrorMessage :: Text
  }
  deriving stock (Generic, Show)

instance ToJSON EvalError where
  toJSON EvalError {..} =
    Aeson.object
      [ "program_id" .= eeProgramId
      , "status" .= eeStatus
      , "error_type" .= eeErrorType
      , "error_message" .= eeErrorMessage
      ]

-- | Parse job ID (UUID) from filename
parseJobId :: FilePath -> Maybe UUID
parseJobId filename =
  let baseName = takeBaseName filename
      -- Handle compound extensions like .uplc.txt or .uplc.flat
      jobIdStr =
        if ".uplc" `isPrefixOf` takeExtension (takeBaseName filename)
          then takeBaseName (takeBaseName filename)
          else baseName
   in UUID.fromString jobIdStr

{-| Check if file is a valid UPLC program file.
Supports two extensions:
- @.uplc.txt@ - Textual UPLC syntax (currently supported)
- @.uplc.flat@ - Flat-encoded binary UPLC (future: requires different parsing path)

TODO [Flat Encoding Support]:
Flat-encoded UPLC files (.uplc.flat) require binary deserialization rather than
text parsing. Flat is a bit-oriented format that's ~35% smaller than CBOR.
Implementation would require:
  1. Detect flat vs text format (by extension or magic bytes)
  2. Use "Flat" package with UPLC.UnrestrictedProgram decoder
  3. Skip the "(program" prefix validation for binary files
Currently, flat files fail with syntax_error (expected MVP behavior). -}
isUplcFile :: FilePath -> Bool
isUplcFile path =
  ".uplc.txt" `isSuffixOf` path || ".uplc.flat" `isSuffixOf` path

{-| Parse a UPLC program from textual syntax.
Returns either a descriptive error message or the parsed program with unit annotations. -}
parseUplcProgram :: Text -> Either Text (UPLC.Program PLC.Name PLC.DefaultUni PLC.DefaultFun ())
parseUplcProgram input =
  case runQuoteT (UPLC.Parser.parseProgram input) of
    Left err -> Left $ T.pack $ show err
    Right prog -> Right $ void prog

{-| Measure execution time of an IO action using criterion-measurement.
Returns the result and execution time in nanoseconds.
Uses evaluate+force to ensure the result is fully evaluated before measuring end time. -}
measureExecution :: NFData a => IO a -> IO (a, Word64)
measureExecution ioAction = do
  startTime <- getTime
  result <- evaluate . force =<< ioAction
  endTime <- getTime
  let timeNs = round ((endTime - startTime) * 1e9) -- Convert seconds to nanoseconds
  return (result, timeNs)

-- | Result of CEK evaluation with budget information
data EvalBudget = EvalBudget
  { ebCpuBudget :: Integer
  , ebMemoryBudget :: Integer
  }
  deriving stock (Generic, Show)

instance NFData EvalBudget

-- | Error that can occur during evaluation
data EvalFailure
  = -- | Failed to convert to NamedDeBruijn
    ConversionError Text
  | -- | CEK evaluation failed
    EvaluationError Text
  deriving stock (Generic, Show)

instance NFData EvalFailure

{-| Convert a parsed UPLC program (with Name) to a term with NamedDeBruijn indices.
This is required for CEK machine evaluation. -}
toNamedDeBruijnTerm
  :: UPLC.Program PLC.Name PLC.DefaultUni PLC.DefaultFun ()
  -> Either EvalFailure (UPLC.Term UPLC.NamedDeBruijn PLC.DefaultUni PLC.DefaultFun ())
toNamedDeBruijnTerm (UPLC.Program _ _ term) =
  case UPLC.deBruijnTerm term of
    Left err -> Left $ ConversionError $ T.pack $ show err
    Right dbTerm -> Right dbTerm

{-| Evaluate a UPLC term using the CEK machine and extract budget costs.
Returns the CPU and memory budget consumed, or an error if evaluation fails. -}
evaluateWithBudget
  :: UPLC.Term UPLC.NamedDeBruijn PLC.DefaultUni PLC.DefaultFun ()
  -> Either EvalFailure EvalBudget
evaluateWithBudget term =
  case Cek.runCekDeBruijn PLC.defaultCekParametersForTesting Cek.tallying Cek.noEmitter term of
    Cek.CekReport res (Cek.TallyingSt _ budget) _logs ->
      case res of
        Cek.CekFailure err ->
          Left $ EvaluationError $ T.pack $ show err
        Cek.CekSuccessConstant _ ->
          Right $ extractBudget budget
        Cek.CekSuccessNonConstant _ ->
          Right $ extractBudget budget
  where
    extractBudget :: ExBudget -> EvalBudget
    extractBudget (ExBudget (ExCPU cpu) (ExMemory mem)) =
      EvalBudget
        { ebCpuBudget = fromSatInt cpu
        , ebMemoryBudget = fromSatInt mem
        }

-- | Number of warm-up iterations before collecting samples
warmupIterations :: Int
warmupIterations = 3

-- | Default number of measurement samples to collect
defaultSampleCount :: Int
defaultSampleCount = 15

{-| Collect multiple timing samples for a UPLC term evaluation.
Performs warm-up iterations first, then collects timing samples.
Budget values are deterministic and returned separately from variable timing data.
Returns early with error if initial validation fails. -}
collectMeasurements
  :: UPLC.Term UPLC.NamedDeBruijn PLC.DefaultUni PLC.DefaultFun ()
  -> Int
  -- ^ Number of samples to collect
  -> IO (Either EvalFailure (EvalBudget, [TimingSample]))
collectMeasurements term sampleCount = do
  -- First, validate the program by evaluating once to get budget (or error)
  case evaluateWithBudget term of
    Left err -> return $ Left err
    Right budget -> do
      -- Perform warm-up iterations (discard results)
      replicateM_ warmupIterations (measureSingleExecution term)

      -- Collect timing samples
      timings <- replicateM sampleCount (measureSingleExecution term)

      -- Build timing samples (only variable timing data)
      let samples = map buildTimingSample timings
      return $ Right (budget, samples)
  where
    -- Measure a single execution and return wall-clock time in nanoseconds
    measureSingleExecution
      :: UPLC.Term UPLC.NamedDeBruijn PLC.DefaultUni PLC.DefaultFun ()
      -> IO Word64
    measureSingleExecution t = do
      (_, timeNs) <- measureExecution $ return $! evalTerm t
      return timeNs

    -- Evaluate term (used for timing, result discarded)
    evalTerm
      :: UPLC.Term UPLC.NamedDeBruijn PLC.DefaultUni PLC.DefaultFun ()
      -> Either EvalFailure EvalBudget
    evalTerm = evaluateWithBudget

    -- Build a TimingSample from timing (only variable data)
    buildTimingSample :: Word64 -> TimingSample
    buildTimingSample cpuTimeNs =
      TimingSample
        { tsCpuTimeNs = cpuTimeNs
        }

-- | Process a single program file
processProgram :: Config -> FilePath -> IO ()
processProgram Config {..} inputPath = do
  let filename = takeFileName inputPath
      baseName = takeBaseName filename
      baseBaseName = takeBaseName baseName -- Handle .uplc.txt -> baseName
  case parseJobId filename of
    Nothing -> do
      hPutStrLn stderr $ "Invalid job ID in filename: " ++ filename
      -- Try to extract some identifier for error reporting
      let jobIdText = T.pack $ take 36 baseBaseName
      writeError
        cfgOutputDir
        jobIdText
        "validation_error"
        "Invalid job ID format in filename. Expected UUID v4 format."
    Just jobId -> do
      let jobIdText = T.pack $ UUID.toString jobId
      hPutStrLn stderr $ "Processing job: " ++ UUID.toString jobId

      -- Read the file content as Text
      -- TODO [Flat Encoding Support]: For .uplc.flat files, read as ByteString
      -- and use binary deserialization instead of text parsing.
      -- See Note [Flat Encoding Support] at isUplcFile.
      readResult <- try @SomeException $ TIO.readFile inputPath

      case readResult of
        Left err -> do
          hPutStrLn stderr $ "Failed to read file: " ++ show err
          writeError
            cfgOutputDir
            jobIdText
            "syntax_error"
            (T.pack $ "Failed to read program file: " ++ show err)
        Right content -> do
          -- Basic validation: check file is not empty
          if T.null content
            then do
              hPutStrLn stderr "Program file is empty"
              writeError
                cfgOutputDir
                jobIdText
                "syntax_error"
                "Program file is empty"
            else do
              -- Check for basic UPLC syntax prefix
              let trimmed = T.dropWhile (`elem` [' ', '\n', '\r', '\t']) content
              if not ("(program" `T.isPrefixOf` trimmed)
                then do
                  hPutStrLn stderr "Program must start with '(program' keyword"
                  writeError
                    cfgOutputDir
                    jobIdText
                    "syntax_error"
                    "Program must start with '(program' keyword"
                else
                  -- Parse UPLC program
                  case parseUplcProgram content of
                    Left parseErr -> do
                      hPutStrLn stderr $ "Parse error: " ++ T.unpack parseErr
                      writeError
                        cfgOutputDir
                        jobIdText
                        "syntax_error"
                        ("Failed to parse program: " <> parseErr)
                    Right program ->
                      -- Convert to NamedDeBruijn representation
                      case toNamedDeBruijnTerm program of
                        Left (ConversionError convErr) -> do
                          hPutStrLn stderr $ "Conversion error: " ++ T.unpack convErr
                          writeError
                            cfgOutputDir
                            jobIdText
                            "evaluation_error"
                            ("Failed to convert program: " <> convErr)
                        Left (EvaluationError evalErr) -> do
                          -- This shouldn't happen in toNamedDeBruijnTerm, but handle it
                          hPutStrLn stderr $ "Evaluation error: " ++ T.unpack evalErr
                          writeError
                            cfgOutputDir
                            jobIdText
                            "evaluation_error"
                            evalErr
                        Right term -> do
                          -- Collect measurements using real CEK evaluation
                          evalResult <- collectMeasurements term defaultSampleCount
                          case evalResult of
                            Left (ConversionError convErr) -> do
                              hPutStrLn stderr $ "Conversion error during evaluation: " ++ T.unpack convErr
                              writeError
                                cfgOutputDir
                                jobIdText
                                "evaluation_error"
                                ("Conversion error: " <> convErr)
                            Left (EvaluationError evalErr) -> do
                              hPutStrLn stderr $ "Evaluation error: " ++ T.unpack evalErr
                              writeError
                                cfgOutputDir
                                jobIdText
                                "evaluation_error"
                                evalErr
                            Right (budget, samples) -> do
                              let result =
                                    EvalResult
                                      { erProgramId = jobIdText
                                      , erStatus = "success"
                                      , erCpuBudget = ebCpuBudget budget
                                      , erMemoryBudget = ebMemoryBudget budget
                                      , -- ExMemory is abstract units; multiply by 8 (word size) as proxy for bytes
                                        erMemoryBytes = ebMemoryBudget budget * 8
                                      , erTimingSamples = samples
                                      }
                              writeResult cfgOutputDir result

      -- Move processed file to avoid reprocessing
      let processedPath = inputPath ++ ".processed"
      renameFile inputPath processedPath
        `catch` \(e :: SomeException) ->
          hPutStrLn stderr $ "Failed to rename file: " ++ show e

-- | Write successful result to JSON file
writeResult :: FilePath -> EvalResult -> IO ()
writeResult outputDir result = do
  let outputPath = outputDir </> T.unpack (erProgramId result) ++ ".result.json"
  BSL.writeFile outputPath (Aeson.encode result)
  hPutStrLn stderr $ "Wrote result: " ++ outputPath

-- | Write error result to JSON file
writeError :: FilePath -> Text -> Text -> Text -> IO ()
writeError outputDir programId errorType errorMessage = do
  let evalError =
        EvalError
          { eeProgramId = programId
          , eeStatus = "error"
          , eeErrorType = errorType
          , eeErrorMessage = errorMessage
          }
      outputPath = outputDir </> T.unpack programId ++ ".error.json"
  BSL.writeFile outputPath (Aeson.encode evalError)
  hPutStrLn stderr $ "Wrote error: " ++ outputPath

-- | Main evaluation loop
evaluationLoop :: Config -> Map FilePath () -> IO ()
evaluationLoop config@Config {..} processedFiles = do
  -- Create directories if they don't exist
  createDirectoryIfMissing True cfgInputDir
  createDirectoryIfMissing True cfgOutputDir

  -- List all files in input directory
  exists <- doesDirectoryExist cfgInputDir
  unless exists do
    hPutStrLn stderr $ "Input directory does not exist: " ++ cfgInputDir
    exitFailure

  allFiles <- listDirectory cfgInputDir
  let inputFiles = filter isUplcFile allFiles
      newFiles = filter (`Map.notMember` processedFiles) inputFiles

  -- Process new files
  newProcessed <-
    foldM
      ( \acc filename -> do
          let fullPath = cfgInputDir </> filename
          isFile <- doesFileExist fullPath
          if isFile
            then do
              processProgram config fullPath
              return $ Map.insert filename () acc
            else return acc
      )
      processedFiles
      newFiles

  -- Wait before next poll
  threadDelay (cfgPollInterval * 1000) -- Convert ms to microseconds

  -- Continue loop
  evaluationLoop config newProcessed

-- | Utility function to extract filename from path
takeFileName :: FilePath -> FilePath
takeFileName = reverse . takeWhile (/= '/') . reverse

-- | Main entry point
main :: IO ()
main = withUtf8 do
  hSetBuffering stderr LineBuffering -- Prevent garbled output from concurrent threads
  initializeTime -- Required before using getTime from criterion-measurement
  config <- execParser opts
  hPutStrLn stderr "UPLC Evaluator Service starting..."
  hPutStrLn stderr $ "Input directory: " ++ cfgInputDir config
  hPutStrLn stderr $ "Output directory: " ++ cfgOutputDir config
  hPutStrLn stderr $ "Poll interval: " ++ show (cfgPollInterval config) ++ "ms"
  evaluationLoop config Map.empty
  where
    opts =
      info
        (configParser <**> helper)
        ( fullDesc
            <> progDesc "UPLC program evaluation service (MVP)"
            <> header "uplc-evaluator - Asynchronous UPLC benchmarking service"
        )
