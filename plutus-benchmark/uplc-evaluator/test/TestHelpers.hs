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
  , waitForFile
  , defaultWaitMs

    -- * Path derivation
  , resultPath
  , errorPath

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

import Control.Concurrent.MVar (newEmptyMVar, takeMVar, tryPutMVar)
import Control.Monad (void, when)
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
import System.Directory (doesFileExist, renameFile)
import System.FSNotify qualified as FS
import System.FilePath (takeDirectory, takeFileName, (</>))
import System.Timeout (timeout)
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
with the naming pattern: {uuid}.uplc.txt

Uses atomic file creation (write to temp, then rename) to prevent
race conditions where the service reads a partially written file. -}
submitProgram :: ServiceHandle -> UUID -> Text -> IO ()
submitProgram ServiceHandle {..} jobId programContent = do
  let filename = UUID.toString jobId ++ ".uplc.txt"
      filepath = shInputDir </> filename
      tempPath = filepath ++ ".tmp"
  -- Write to temp file first, then atomically rename
  writeFile tempPath (T.unpack programContent)
  renameFile tempPath filepath

{-| Submit a flat-encoded UPLC program

Writes the binary content to a file in the service's input directory
with the naming pattern: {uuid}.uplc.flat

Uses atomic file creation (write to temp, then rename) to prevent
race conditions where the service reads a partially written file. -}
submitProgramFlat :: ServiceHandle -> UUID -> ByteString -> IO ()
submitProgramFlat ServiceHandle {..} jobId programBytes = do
  let filename = UUID.toString jobId ++ ".uplc.flat"
      filepath = shInputDir </> filename
      tempPath = filepath ++ ".tmp"
  -- Write to temp file first, then atomically rename
  BS.writeFile tempPath programBytes
  renameFile tempPath filepath

-- | Path the service writes a result.json to for this job.
resultPath :: ServiceHandle -> UUID -> FilePath
resultPath ServiceHandle {..} jobId =
  shOutputDir </> UUID.toString jobId ++ ".result.json"

-- | Path the service writes an error.json to for this job.
errorPath :: ServiceHandle -> UUID -> FilePath
errorPath ServiceHandle {..} jobId =
  shOutputDir </> UUID.toString jobId ++ ".error.json"

{-| Wait for a result.json file to appear

Subscribes to filesystem events for the output directory and returns as soon
as the file is created, with 'defaultWaitMs' as a safety-net timeout.
Returns the filepath if found, Nothing if timeout. -}
waitForResult :: ServiceHandle -> UUID -> IO (Maybe FilePath)
waitForResult handle jobId = waitForFile (resultPath handle jobId) defaultWaitMs

{-| Wait for an error.json file to appear

Subscribes to filesystem events for the output directory and returns as soon
as the file is created, with 'defaultWaitMs' as a safety-net timeout.
Returns the filepath if found, Nothing if timeout. -}
waitForError :: ServiceHandle -> UUID -> IO (Maybe FilePath)
waitForError handle jobId = waitForFile (errorPath handle jobId) defaultWaitMs

{-| Wait for a file to appear, event-driven

Registers an fsnotify watcher on the parent directory and blocks until the
file appears, with a wall-clock safety net. A post-registration existence
check closes the race window where the file is created after the watcher is
set up but before an event is observed. Timeout is specified in milliseconds. -}
waitForFile :: FilePath -> Int -> IO (Maybe FilePath)
waitForFile filepath timeoutMs = do
  done <- newEmptyMVar
  let dir = takeDirectory filepath
      target = takeFileName filepath
      isMatch ev = takeFileName (FS.eventPath ev) == target
  FS.withManager $ \mgr -> do
    stop <- FS.watchDir mgr dir isMatch (\_ -> void (tryPutMVar done ()))
    -- The file may have appeared before the watcher started; check once
    -- after registering so we don't deadlock waiting for a missed event.
    alreadyThere <- doesFileExist filepath
    when alreadyThere (void (tryPutMVar done ()))
    res <- timeout (timeoutMs * 1000) (takeMVar done)
    stop
    pure (filepath <$ res)

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

{-| Default upper bound for "wait until the service produces output".
Generous enough to absorb scheduler jitter on loaded CI builders;
the event-driven waiter returns immediately on success, so this is
only paid on actual hangs. -}
defaultWaitMs :: Int
defaultWaitMs = 20000

{-| Wait for a result file and fail the test if it does not appear

This is a convenience wrapper around waitForResult that converts
timeout to a test failure using assertFailure. -}
waitForResultOrFail :: ServiceHandle -> UUID -> IO FilePath
waitForResultOrFail handle jobId = do
  result <- waitForResult handle jobId
  maybe (assertFailure "Timeout waiting for result.json") pure result

{-| Wait for an error file and fail the test if it does not appear

This is a convenience wrapper around waitForError that converts
timeout to a test failure using assertFailure. -}
waitForErrorOrFail :: ServiceHandle -> UUID -> IO FilePath
waitForErrorOrFail handle jobId = do
  result <- waitForError handle jobId
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
