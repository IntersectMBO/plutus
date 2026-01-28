{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeApplications #-}

module Main (main) where

import Control.Concurrent (threadDelay)
import Control.Exception (SomeException, catch, try)
import Control.Monad (foldM, unless, when)
import Data.Aeson (ToJSON (..), (.=))
import Data.Aeson qualified as Aeson
import Data.ByteString.Lazy qualified as BSL
import Data.List (isPrefixOf, isSuffixOf)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Text (Text)
import Data.Text qualified as T
import Data.UUID (UUID)
import Data.UUID qualified as UUID
import GHC.Generics (Generic)
import Main.Utf8 (withUtf8)
import Options.Applicative
import System.Directory
import System.Exit (exitFailure)
import System.FilePath (takeBaseName, takeExtension, (</>))
import System.IO (hPutStrLn, stderr)
import System.Random (randomRIO)

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

-- | Measurement data for a single evaluation run
data Measurement = Measurement
  { mCpuTimeMs :: Double
  , mMemoryBytes :: Integer
  , mCpuBudget :: Integer
  , mMemoryBudget :: Integer
  }
  deriving stock (Generic, Show)

instance ToJSON Measurement where
  toJSON Measurement {..} =
    Aeson.object
      [ "cpu_time_ms" .= mCpuTimeMs
      , "memory_bytes" .= mMemoryBytes
      , "cpu_budget" .= mCpuBudget
      , "memory_budget" .= mMemoryBudget
      ]

-- | Successful evaluation result
data EvalResult = EvalResult
  { erProgramId :: Text
  , erStatus :: Text
  , erMeasurements :: [Measurement]
  }
  deriving stock (Generic, Show)

instance ToJSON EvalResult where
  toJSON EvalResult {..} =
    Aeson.object
      [ "program_id" .= erProgramId
      , "status" .= erStatus
      , "measurements" .= erMeasurements
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

-- | Check if file is a valid UPLC program file
isUplcFile :: FilePath -> Bool
isUplcFile path =
  ".uplc.txt" `isSuffixOf` path || ".uplc.flat" `isSuffixOf` path

-- | Generate deterministic/random measurements for MVP
generateMeasurements :: IO [Measurement]
generateMeasurements = do
  -- Generate 10-20 samples
  numSamples <- randomRIO (10, 20 :: Int)
  mapM (const generateSingleMeasurement) [1 .. numSamples]
  where
    generateSingleMeasurement :: IO Measurement
    generateSingleMeasurement = do
      -- Generate realistic-looking random values
      -- CPU time: 0.1ms to 500ms
      cpuTime <- randomRIO (0.1, 500.0)
      -- Memory: 1KB to 10MB
      memory <- randomRIO (1024, 10485760)
      -- CPU budget: 1000 to 100M ExCPU units
      cpuBudget <- randomRIO (1000, 100000000)
      -- Memory budget: 1000 to 50M ExMemory units
      memBudget <- randomRIO (1000, 50000000)
      return $
        Measurement
          { mCpuTimeMs = cpuTime
          , mMemoryBytes = memory
          , mCpuBudget = cpuBudget
          , mMemoryBudget = memBudget
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

      -- Read and validate the file (basic checks)
      result <- try @SomeException do
        content <- readFile inputPath
        -- Basic validation: check file is not empty
        when (null content) $
          error "Program file is empty"
        -- Check for basic UPLC syntax (very simple check for MVP)
        -- UPLC programs start with "(program" - check after stripping whitespace
        let trimmed = dropWhile (`elem` [' ', '\n', '\r', '\t']) content
        unless ("(program" `isPrefixOf` trimmed) $
          error "Program must start with '(program' keyword"
        return content

      case result of
        Left err -> do
          hPutStrLn stderr $ "Validation error: " ++ show err
          writeError
            cfgOutputDir
            jobIdText
            "syntax_error"
            (T.pack $ "Failed to parse program: " ++ show err)
        Right _ -> do
          -- Generate measurements (MVP: random values)
          measurements <- generateMeasurements
          let evalResult =
                EvalResult
                  { erProgramId = jobIdText
                  , erStatus = "success"
                  , erMeasurements = measurements
                  }
          writeResult cfgOutputDir evalResult

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
