{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}

module TestHelpers
  ( -- * Submission functions
    submitProgram
  , submitProgramFlat

    -- * Waiting functions
  , waitForResult
  , waitForError
  , waitForResultOrFail
  , waitForErrorOrFail

    -- * JSON parsing functions
  , readResultJson
  , readErrorJson
  , readResultJsonOrFail
  , readErrorJsonOrFail

    -- * Types
  , EvalResult (..)
  , EvalError (..)
  , TimingSample (..)
  ) where

import Control.Concurrent (threadDelay)
import Data.Aeson (FromJSON (..), (.:))
import Data.Aeson qualified as Aeson
import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Data.ByteString.Lazy qualified as BSL
import Data.Text (Text)
import Data.Text qualified as T
import Data.UUID (UUID)
import Data.UUID qualified as UUID
import Data.Word (Word64)
import GHC.Generics (Generic)
import Harness (ServiceHandle (..))
import System.Directory (doesFileExist)
import System.FilePath ((</>))
import Test.Tasty.HUnit (assertFailure)

-- | Timing sample for a single evaluation run (variable data only)
newtype TimingSample = TimingSample
  { tsCpuTimeNs :: Word64
  }
  deriving stock (Generic, Show, Eq)

instance FromJSON TimingSample where
  parseJSON = Aeson.withObject "TimingSample" \v ->
    TimingSample
      <$> v .: "cpu_time_ns"

-- | Successful evaluation result with deterministic budget at top level
data EvalResult = EvalResult
  { erProgramId :: Text
  , erStatus :: Text
  , erCpuBudget :: Integer
  , erMemoryBudget :: Integer
  , erMemoryBytes :: Integer
  , erTimingSamples :: [TimingSample]
  }
  deriving stock (Generic, Show, Eq)

instance FromJSON EvalResult where
  parseJSON = Aeson.withObject "EvalResult" \v ->
    EvalResult
      <$> v .: "program_id"
      <*> v .: "status"
      <*> v .: "cpu_budget"
      <*> v .: "memory_budget"
      <*> v .: "memory_bytes"
      <*> v .: "timing_samples"

-- | Error result
data EvalError = EvalError
  { eeProgramId :: Text
  , eeStatus :: Text
  , eeErrorType :: Text
  , eeErrorMessage :: Text
  }
  deriving stock (Generic, Show, Eq)

instance FromJSON EvalError where
  parseJSON = Aeson.withObject "EvalError" \v ->
    EvalError
      <$> v .: "program_id"
      <*> v .: "status"
      <*> v .: "error_type"
      <*> v .: "error_message"

{-| Submit a textual UPLC program

Writes the program content to a file in the service's input directory
with the naming pattern: {uuid}.uplc.txt -}
submitProgram :: ServiceHandle -> UUID -> Text -> IO ()
submitProgram ServiceHandle {..} jobId programContent = do
  let filename = UUID.toString jobId ++ ".uplc.txt"
      filepath = shInputDir </> filename
  writeFile filepath (T.unpack programContent)

{-| Submit a flat-encoded UPLC program

Writes the binary content to a file in the service's input directory
with the naming pattern: {uuid}.uplc.flat -}
submitProgramFlat :: ServiceHandle -> UUID -> ByteString -> IO ()
submitProgramFlat ServiceHandle {..} jobId programBytes = do
  let filename = UUID.toString jobId ++ ".uplc.flat"
      filepath = shInputDir </> filename
  BS.writeFile filepath programBytes

{-| Wait for a result.json file to appear

Polls the output directory until the result file appears or timeout is reached.
Timeout is specified in milliseconds.
Returns the filepath if found, Nothing if timeout. -}
waitForResult :: ServiceHandle -> UUID -> Int -> IO (Maybe FilePath)
waitForResult ServiceHandle {..} jobId timeoutMs = do
  let filename = UUID.toString jobId ++ ".result.json"
      filepath = shOutputDir </> filename
      -- Convert timeout to microseconds for threadDelay
      timeoutUs = timeoutMs * 1000
      -- Poll every 50ms
      pollIntervalUs = 50000
  waitForFile filepath timeoutUs pollIntervalUs

{-| Wait for an error.json file to appear

Polls the output directory until the error file appears or timeout is reached.
Timeout is specified in milliseconds.
Returns the filepath if found, Nothing if timeout. -}
waitForError :: ServiceHandle -> UUID -> Int -> IO (Maybe FilePath)
waitForError ServiceHandle {..} jobId timeoutMs = do
  let filename = UUID.toString jobId ++ ".error.json"
      filepath = shOutputDir </> filename
      timeoutUs = timeoutMs * 1000
      pollIntervalUs = 50000
  waitForFile filepath timeoutUs pollIntervalUs

{-| Internal helper to wait for a file to appear

Polls at regular intervals until file exists or timeout. -}
waitForFile :: FilePath -> Int -> Int -> IO (Maybe FilePath)
waitForFile filepath timeoutUs pollIntervalUs = go 0
  where
    go elapsedUs = do
      exists <- doesFileExist filepath
      if exists
        then return (Just filepath)
        else
          if elapsedUs >= timeoutUs
            then return Nothing
            else do
              threadDelay pollIntervalUs
              go (elapsedUs + pollIntervalUs)

{-| Read and parse a result JSON file

Returns the parsed EvalResult or an error message. -}
readResultJson :: FilePath -> IO (Either String EvalResult)
readResultJson filepath = do
  content <- BSL.readFile filepath
  return $ Aeson.eitherDecode content

{-| Read and parse an error JSON file

Returns the parsed EvalError or an error message. -}
readErrorJson :: FilePath -> IO (Either String EvalError)
readErrorJson filepath = do
  content <- BSL.readFile filepath
  return $ Aeson.eitherDecode content

{-| Wait for a result file and fail the test if timeout

This is a convenience wrapper around waitForResult that converts
timeout to a test failure using assertFailure. -}
waitForResultOrFail :: ServiceHandle -> UUID -> Int -> IO FilePath
waitForResultOrFail handle jobId timeoutMs = do
  result <- waitForResult handle jobId timeoutMs
  maybe (assertFailure "Timeout waiting for result.json") pure result

{-| Wait for an error file and fail the test if timeout

This is a convenience wrapper around waitForError that converts
timeout to a test failure using assertFailure. -}
waitForErrorOrFail :: ServiceHandle -> UUID -> Int -> IO FilePath
waitForErrorOrFail handle jobId timeoutMs = do
  result <- waitForError handle jobId timeoutMs
  maybe (assertFailure "Timeout waiting for error.json") pure result

{-| Read and parse a result JSON file, failing the test on error

This is a convenience wrapper around readResultJson that converts
parsing errors to test failures using assertFailure. -}
readResultJsonOrFail :: FilePath -> IO EvalResult
readResultJsonOrFail filepath = do
  result <- readResultJson filepath
  either (\err -> assertFailure $ "Failed to parse result JSON: " ++ err) pure result

{-| Read and parse an error JSON file, failing the test on error

This is a convenience wrapper around readErrorJson that converts
parsing errors to test failures using assertFailure. -}
readErrorJsonOrFail :: FilePath -> IO EvalError
readErrorJsonOrFail filepath = do
  result <- readErrorJson filepath
  either (\err -> assertFailure $ "Failed to parse error JSON: " ++ err) pure result
