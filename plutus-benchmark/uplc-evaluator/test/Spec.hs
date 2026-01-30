{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes #-}

module Main (main) where

import Control.Concurrent (threadDelay)
import Data.List (nub)
import Data.String.Interpolate (__i)
import Data.Text qualified as T
import Data.UUID qualified as UUID
import Data.UUID.V4 qualified as UUID
import Harness (ServiceHandle (..), findEvaluatorExecutable, withEvaluatorService)
import Main.Utf8 (withUtf8)
import System.Directory (doesDirectoryExist, doesFileExist, listDirectory)
import System.FilePath ((</>))
import System.IO (BufferMode (LineBuffering), hSetBuffering, stderr, stdout)
import Test.Tasty (defaultMain, testGroup)
import Test.Tasty.HUnit (assertBool, assertFailure, testCase, (@?=))
import TestHelpers
  ( EvalError (..)
  , EvalResult (..)
  , TimingSample (..)
  , readErrorJsonOrFail
  , readResultJson
  , readResultJsonOrFail
  , submitProgram
  , submitProgramFlat
  , waitForError
  , waitForErrorOrFail
  , waitForResult
  , waitForResultOrFail
  )

main :: IO ()
main = withUtf8 do
  -- Prevent garbled output from concurrent test execution
  hSetBuffering stdout LineBuffering
  hSetBuffering stderr LineBuffering
  defaultMain
    ( testGroup
        "uplc-evaluator integration tests"
        [ testGroup
            "Infrastructure"
            [ testCase "Basic scaffolding test" do
                -- This is a basic test to verify the test infrastructure is set up correctly
                let expected :: Integer = 2 + 2; actual = 4
                actual @?= expected
            , testCase "Service lifecycle - start and stop" do
                -- Test that the service can start and stop cleanly
                execPath <- findEvaluatorExecutable
                withEvaluatorService execPath \handle -> do
                  -- Verify input directory exists
                  inputExists <- doesDirectoryExist (shInputDir handle)
                  assertBool "Input directory should exist" inputExists

                  -- Verify output directory exists
                  outputExists <- doesDirectoryExist (shOutputDir handle)
                  assertBool "Output directory should exist" outputExists
            ]
        , testGroup
            "Textual UPLC Programs"
            [ testCase "Successful evaluation of simple textual program" do
                execPath <- findEvaluatorExecutable
                withEvaluatorService execPath \handle -> do
                  -- Generate a UUID for this job
                  jobId <- UUID.nextRandom

                  -- Submit a valid UPLC program
                  let program = "(program 1.0.0 (con integer 42))"
                  submitProgram handle jobId program

                  -- Wait for result (5 second timeout)
                  path <- waitForResultOrFail handle jobId 5000
                  result <- readResultJsonOrFail path

                  -- Verify program_id matches submitted UUID
                  let expectedId = T.pack (UUID.toString jobId)
                  erProgramId result @?= expectedId

                  -- Verify status is "success"
                  erStatus result @?= "success"

                  -- Verify top-level budget fields are positive
                  assertBool
                    ("cpu_budget should be > 0, got " ++ show (erCpuBudget result))
                    (erCpuBudget result > 0)
                  assertBool
                    ("memory_budget should be > 0, got " ++ show (erMemoryBudget result))
                    (erMemoryBudget result > 0)
                  assertBool
                    ("memory_bytes should be > 0, got " ++ show (erMemoryBytes result))
                    (erMemoryBytes result > 0)

                  -- Verify timing_samples array has 10-20 entries
                  let sampleCount = length (erTimingSamples result)
                  assertBool
                    ("timing_samples should have 10-20 entries, got " ++ show sampleCount)
                    (sampleCount >= 10 && sampleCount <= 20)

                  -- Verify each timing sample has non-negative cpu_time_ns
                  -- Note: Very fast evaluations can report 0ns due to measurement resolution
                  mapM_
                    ( \s -> do
                        -- Check that cpu_time_ns is in reasonable range (>= 0, bounded above)
                        assertBool
                          ("cpu_time_ns should be >= 0, got " ++ show (tsCpuTimeNs s))
                          (tsCpuTimeNs s >= 0)
                    )
                    (erTimingSamples result)

                  -- Verify original input file is renamed to .processed
                  let inputFilename = UUID.toString jobId ++ ".uplc.txt"
                      inputPath = shInputDir handle </> inputFilename
                      processedPath = inputPath ++ ".processed"
                  inputExists <- doesFileExist inputPath
                  processedExists <- doesFileExist processedPath
                  assertBool "Original input file should not exist" (not inputExists)
                  assertBool "Processed file should exist" processedExists
            ]
        , testGroup
            "Flat-encoded UPLC Programs"
            [ testCase "Flat-encoded file produces syntax error (MVP limitation)" do
                execPath <- findEvaluatorExecutable
                withEvaluatorService execPath \handle -> do
                  -- Generate a UUID for this job
                  jobId <- UUID.nextRandom

                  -- Submit a flat-encoded binary file
                  -- Note: In MVP, the service reads files as text and checks for "(program" prefix
                  -- Real flat-encoded UPLC starts with specific binary markers, not text
                  -- For testing, we'll use non-empty binary data that doesn't start with "(program"
                  let flatBytes = "\x01\x00\x00\x00\x01\x00\x00\x00" -- 8 bytes of binary data
                  submitProgramFlat handle jobId flatBytes

                  -- Wait for error (5 second timeout)
                  -- Expected: MVP validates text content, flat binary won't have "(program" prefix
                  path <- waitForErrorOrFail handle jobId 5000
                  evalError <- readErrorJsonOrFail path

                  -- Verify program_id matches submitted UUID
                  let expectedId = T.pack (UUID.toString jobId)
                  eeProgramId evalError @?= expectedId

                  -- Verify status is "error"
                  eeStatus evalError @?= "error"

                  -- Verify error type is "syntax_error"
                  -- MVP limitation: reads binary as text, doesn't find "(program" prefix
                  eeErrorType evalError @?= "syntax_error"

                  -- Verify error message mentions the validation issue
                  assertBool
                    "Error message should mention program validation"
                    ( T.isInfixOf "program" (T.toLower (eeErrorMessage evalError))
                        || T.isInfixOf "parse" (T.toLower (eeErrorMessage evalError))
                    )

                  -- Verify original input file is renamed to .processed
                  let inputFilename = UUID.toString jobId ++ ".uplc.flat"
                      inputPath = shInputDir handle </> inputFilename
                      processedPath = inputPath ++ ".processed"
                  inputExists <- doesFileExist inputPath
                  processedExists <- doesFileExist processedPath
                  assertBool "Original input file should not exist" (not inputExists)
                  assertBool "Processed file should exist" processedExists
            ]
        , testGroup
            "Error Handling"
            [ testCase "Empty file produces syntax error" do
                execPath <- findEvaluatorExecutable
                withEvaluatorService execPath \handle -> do
                  -- Generate a UUID for this job
                  jobId <- UUID.nextRandom

                  -- Submit an empty file
                  let emptyProgram = ""
                  submitProgram handle jobId emptyProgram

                  -- Wait for error (5 second timeout)
                  path <- waitForErrorOrFail handle jobId 5000
                  evalError <- readErrorJsonOrFail path

                  -- Verify program_id matches submitted UUID
                  let expectedId = T.pack (UUID.toString jobId)
                  eeProgramId evalError @?= expectedId

                  -- Verify status is "error"
                  eeStatus evalError @?= "error"

                  -- Verify error type is "syntax_error"
                  eeErrorType evalError @?= "syntax_error"

                  -- Verify error message mentions empty file
                  assertBool
                    "Error message should mention empty or invalid content"
                    ( T.isInfixOf "empty" (T.toLower (eeErrorMessage evalError))
                        || T.isInfixOf "program" (T.toLower (eeErrorMessage evalError))
                    )
            , testCase "Invalid syntax - garbage content produces syntax error" do
                execPath <- findEvaluatorExecutable
                withEvaluatorService execPath \handle -> do
                  -- Generate a UUID for this job
                  jobId <- UUID.nextRandom

                  -- Submit a file with invalid content
                  let invalidProgram = "not a valid program"
                  submitProgram handle jobId invalidProgram

                  -- Wait for error (5 second timeout)
                  path <- waitForErrorOrFail handle jobId 5000
                  evalError <- readErrorJsonOrFail path
                  -- Verify program_id matches submitted UUID
                  let expectedId = T.pack (UUID.toString jobId)
                  eeProgramId evalError @?= expectedId

                  -- Verify status is "error"
                  eeStatus evalError @?= "error"

                  -- Verify error type is "syntax_error"
                  eeErrorType evalError @?= "syntax_error"

                  -- Verify error message mentions program validation
                  assertBool
                    "Error message should mention (program requirement"
                    (T.isInfixOf "program" (T.toLower (eeErrorMessage evalError)))
            , testCase "Invalid syntax - missing opening parenthesis produces syntax error" do
                execPath <- findEvaluatorExecutable
                withEvaluatorService execPath \handle -> do
                  -- Generate a UUID for this job
                  jobId <- UUID.nextRandom

                  -- Submit a program missing the opening parenthesis
                  -- This should fail because UPLC syntax requires "(program" not just "program"
                  let invalidProgram = "program 1.0.0 (con integer 42)"
                  submitProgram handle jobId invalidProgram

                  -- Wait for error (5 second timeout)
                  path <- waitForErrorOrFail handle jobId 5000
                  evalError <- readErrorJsonOrFail path
                  -- Verify program_id matches submitted UUID
                  let expectedId = T.pack (UUID.toString jobId)
                  eeProgramId evalError @?= expectedId

                  -- Verify status is "error"
                  eeStatus evalError @?= "error"

                  -- Verify error type is "syntax_error"
                  eeErrorType evalError @?= "syntax_error"

                  -- Verify error message mentions (program requirement
                  assertBool
                    "Error message should mention (program requirement"
                    (T.isInfixOf "(program" (T.toLower (eeErrorMessage evalError)))
            , testCase "Invalid UUID - filename 'not-a-uuid.uplc.txt' produces validation error" do
                execPath <- findEvaluatorExecutable
                withEvaluatorService execPath \handle -> do
                  -- Submit a file with an invalid UUID filename
                  let invalidFilename = "not-a-uuid.uplc.txt"
                      inputPath = shInputDir handle </> invalidFilename
                      program = "(program 1.0.0 (con integer 42))"
                  writeFile inputPath program

                  -- Service will extract "not-a-uuid" as the job ID (first 36 chars of base name)
                  let expectedJobId = "not-a-uuid"
                      errorFilename = expectedJobId ++ ".error.json"
                      errorPath = shOutputDir handle </> errorFilename

                  -- Wait for error file (5 second timeout)
                  path <-
                    maybe (assertFailure "Timeout waiting for error.json") pure
                      =<< waitForFileWithTimeout errorPath 5000
                  evalError <- readErrorJsonOrFail path
                  -- Verify program_id matches truncated filename
                  eeProgramId evalError @?= T.pack expectedJobId

                  -- Verify status is "error"
                  eeStatus evalError @?= "error"

                  -- Verify error type is "validation_error"
                  eeErrorType evalError @?= "validation_error"

                  -- Verify error message mentions invalid UUID format
                  assertBool
                    "Error message should mention UUID or job ID format"
                    ( T.isInfixOf "uuid" (T.toLower (eeErrorMessage evalError))
                        || T.isInfixOf "job id" (T.toLower (eeErrorMessage evalError))
                    )
            , testCase "Invalid UUID - filename 'job-123.uplc.txt' produces validation error" do
                execPath <- findEvaluatorExecutable
                withEvaluatorService execPath \handle -> do
                  -- Submit a file with a non-UUID filename
                  let invalidFilename = "job-123.uplc.txt"
                      inputPath = shInputDir handle </> invalidFilename
                      program = "(program 1.0.0 (con integer 42))"
                  writeFile inputPath program

                  -- Service will extract "job-123" as the job ID
                  let expectedJobId = "job-123"
                      errorFilename = expectedJobId ++ ".error.json"
                      errorPath = shOutputDir handle </> errorFilename

                  -- Wait for error file (5 second timeout)
                  path <-
                    maybe (assertFailure "Timeout waiting for error.json") pure
                      =<< waitForFileWithTimeout errorPath 5000
                  evalError <- readErrorJsonOrFail path
                  -- Verify program_id matches truncated filename
                  eeProgramId evalError @?= T.pack expectedJobId

                  -- Verify status is "error"
                  eeStatus evalError @?= "error"

                  -- Verify error type is "validation_error"
                  eeErrorType evalError @?= "validation_error"

                  -- Verify error message mentions invalid format
                  assertBool
                    "Error message should mention UUID or format"
                    ( T.isInfixOf "uuid" (T.toLower (eeErrorMessage evalError))
                        || T.isInfixOf "format" (T.toLower (eeErrorMessage evalError))
                    )
            , testCase "Invalid UUID - filename '12345.uplc.txt' produces validation error" do
                execPath <- findEvaluatorExecutable
                withEvaluatorService execPath \handle -> do
                  -- Submit a file with numbers-only filename (not UUID format)
                  let invalidFilename = "12345.uplc.txt"
                      inputPath = shInputDir handle </> invalidFilename
                      program = "(program 1.0.0 (con integer 42))"
                  writeFile inputPath program

                  -- Service will extract "12345" as the job ID
                  let expectedJobId = "12345"
                      errorFilename = expectedJobId ++ ".error.json"
                      errorPath = shOutputDir handle </> errorFilename

                  -- Wait for error file (5 second timeout)
                  path <-
                    maybe (assertFailure "Timeout waiting for error.json") pure
                      =<< waitForFileWithTimeout errorPath 5000
                  evalError <- readErrorJsonOrFail path
                  -- Verify program_id matches truncated filename
                  eeProgramId evalError @?= T.pack expectedJobId

                  -- Verify status is "error"
                  eeStatus evalError @?= "error"

                  -- Verify error type is "validation_error"
                  eeErrorType evalError @?= "validation_error"

                  -- Verify error message mentions format requirement
                  assertBool
                    "Error message should mention UUID v4 format"
                    ( T.isInfixOf "uuid" (T.toLower (eeErrorMessage evalError))
                        || T.isInfixOf "format" (T.toLower (eeErrorMessage evalError))
                    )
            , testCase "Runtime evaluation error produces evaluation_error" do
                execPath <- findEvaluatorExecutable
                withEvaluatorService execPath \handle -> do
                  -- Generate a UUID for this job
                  jobId <- UUID.nextRandom

                  -- Submit a syntactically valid program that causes a runtime error
                  -- This tries to apply an integer constant (42) to an argument (1)
                  -- which fails at runtime because an integer is not a function
                  let program = "(program 1.0.0 [ (con integer 42) (con integer 1) ])"
                  submitProgram handle jobId program

                  -- Wait for error (5 second timeout)
                  path <- waitForErrorOrFail handle jobId 5000
                  evalError <- readErrorJsonOrFail path

                  -- Verify program_id matches submitted UUID
                  let expectedId = T.pack (UUID.toString jobId)
                  eeProgramId evalError @?= expectedId

                  -- Verify status is "error"
                  eeStatus evalError @?= "error"

                  -- Verify error type is "evaluation_error" (not "syntax_error")
                  -- This is a runtime error, not a parse error
                  eeErrorType evalError @?= "evaluation_error"

                  -- Verify error message contains descriptive information
                  -- The CEK machine should report something about applying a non-function
                  assertBool
                    "Error message should contain descriptive information"
                    (not $ T.null $ eeErrorMessage evalError)
            ]
        , testGroup
            "File Filtering"
            [ testCase "Files without .uplc.txt or .uplc.flat extension are ignored" do
                execPath <- findEvaluatorExecutable
                withEvaluatorService execPath \handle -> do
                  -- Generate UUIDs for test files
                  jobId1 <- UUID.nextRandom
                  jobId2 <- UUID.nextRandom
                  jobId3 <- UUID.nextRandom

                  -- Submit files with incorrect extensions
                  let program = "(program 1.0.0 (con integer 42))"
                      -- File with .txt only (not .uplc.txt)
                      txtOnlyPath = shInputDir handle </> UUID.toString jobId1 ++ ".txt"
                      -- File with .json extension
                      jsonPath = shInputDir handle </> UUID.toString jobId2 ++ ".json"
                      -- File with .uplc.config extension
                      configPath = shInputDir handle </> UUID.toString jobId3 ++ ".uplc.config"

                  writeFile txtOnlyPath program
                  writeFile jsonPath program
                  writeFile configPath program

                  -- Wait 2 seconds to ensure service has time to process (if it were to)
                  threadDelay 2000000 -- 2 seconds in microseconds

                  -- Verify none of these produced result or error files
                  result1 <- waitForResult handle jobId1 100 -- Short timeout, should already exist if processed
                  result2 <- waitForResult handle jobId2 100
                  result3 <- waitForResult handle jobId3 100
                  error1 <- waitForError handle jobId1 100
                  error2 <- waitForError handle jobId2 100
                  error3 <- waitForError handle jobId3 100

                  -- All should be Nothing (not processed)
                  case result1 of
                    Just _ -> assertFailure ".txt file should not be processed"
                    Nothing -> return ()
                  case result2 of
                    Just _ -> assertFailure ".json file should not be processed"
                    Nothing -> return ()
                  case result3 of
                    Just _ -> assertFailure ".uplc.config file should not be processed"
                    Nothing -> return ()
                  case error1 of
                    Just _ -> assertFailure ".txt file should not produce error"
                    Nothing -> return ()
                  case error2 of
                    Just _ -> assertFailure ".json file should not produce error"
                    Nothing -> return ()
                  case error3 of
                    Just _ -> assertFailure ".uplc.config file should not produce error"
                    Nothing -> return ()
            , testCase "Valid .uplc.txt file is processed alongside ignored files" do
                execPath <- findEvaluatorExecutable
                withEvaluatorService execPath \handle -> do
                  -- Generate UUIDs
                  validJobId <- UUID.nextRandom
                  ignoredJobId <- UUID.nextRandom

                  let program = "(program 1.0.0 (con integer 42))"
                      -- Valid .uplc.txt file
                      validPath = shInputDir handle </> UUID.toString validJobId ++ ".uplc.txt"
                      -- File with wrong extension
                      ignoredPath = shInputDir handle </> UUID.toString ignoredJobId ++ ".txt"

                  -- Submit both files
                  writeFile validPath program
                  writeFile ignoredPath program

                  -- Wait for the valid file to be processed
                  path <-
                    maybe (assertFailure "Valid .uplc.txt file should be processed") pure
                      =<< waitForResult handle validJobId 5000
                  result <- readResultJsonOrFail path
                  erStatus result @?= "success"

                  -- Verify the ignored file was not processed
                  ignoredResult <- waitForResult handle ignoredJobId 100
                  case ignoredResult of
                    Just _ -> assertFailure "File with wrong extension should not be processed"
                    Nothing -> return ()
            ]
        , testGroup
            "Measurement Data Validation"
            [ testCase "Measurement data follows expected ranges and structure" do
                execPath <- findEvaluatorExecutable
                withEvaluatorService execPath \handle -> do
                  -- Generate a UUID for this job
                  jobId <- UUID.nextRandom

                  -- Submit a valid UPLC program
                  let program = "(program 1.0.0 (con integer 42))"
                  submitProgram handle jobId program

                  -- Wait for result (5 second timeout)
                  path <- waitForResultOrFail handle jobId 5000
                  result <- readResultJsonOrFail path
                  -- Verify timing_samples array has 10-20 entries
                  let samples = erTimingSamples result
                      sampleCount = length samples
                  assertBool
                    ("timing_samples should have 10-20 entries, got " ++ show sampleCount)
                    (sampleCount >= 10 && sampleCount <= 20)

                  -- Verify top-level budget values are in expected ranges
                  -- Note: With real CEK evaluation, simple programs have small budget values.
                  let cpuBudget = erCpuBudget result
                  assertBool
                    ("cpu_budget should be >= 0 and <= 100000000, got " ++ show cpuBudget)
                    (cpuBudget >= 0 && cpuBudget <= 100000000)

                  let memBudget = erMemoryBudget result
                  assertBool
                    ("memory_budget should be >= 0 and <= 50000000, got " ++ show memBudget)
                    (memBudget >= 0 && memBudget <= 50000000)

                  -- memory_bytes is derived from ExMemory * 8 (word size)
                  let memBytes = erMemoryBytes result
                  assertBool
                    ("memory_bytes should be >= 0 and <= 10485760, got " ++ show memBytes)
                    (memBytes >= 0 && memBytes <= 10485760)

                  -- Verify each timing sample has cpu_time_ns in expected range
                  -- Simple programs can evaluate in microseconds
                  mapM_
                    ( \s -> do
                        let cpuTime = tsCpuTimeNs s
                        assertBool
                          ("cpu_time_ns should be >= 0 and <= 500000000, got " ++ show cpuTime)
                          (cpuTime >= 0 && cpuTime <= 500000000)
                    )
                    samples
            ]
        , testGroup
            "Budget Determinism"
            [ testCase "Budget values are at top level (deterministic, not repeated in samples)" do
                execPath <- findEvaluatorExecutable
                withEvaluatorService execPath \handle -> do
                  -- Generate a UUID for this job
                  jobId <- UUID.nextRandom

                  -- Submit a valid UPLC program
                  let program = "(program 1.0.0 (con integer 42))"
                  submitProgram handle jobId program

                  -- Wait for result (5 second timeout)
                  path <- waitForResultOrFail handle jobId 5000
                  result <- readResultJsonOrFail path
                  -- Verify we have timing samples
                  let samples = erTimingSamples result
                      sampleCount = length samples
                  assertBool
                    ("Should have at least 10 timing samples, got " ++ show sampleCount)
                    (sampleCount >= 10)

                  -- Budget values are now at top level (single deterministic value)
                  -- Just verify they exist and are positive
                  assertBool
                    ("cpu_budget should be > 0, got " ++ show (erCpuBudget result))
                    (erCpuBudget result > 0)
                  assertBool
                    ("memory_budget should be > 0, got " ++ show (erMemoryBudget result))
                    (erMemoryBudget result > 0)
                  assertBool
                    ("memory_bytes should be > 0, got " ++ show (erMemoryBytes result))
                    (erMemoryBytes result > 0)

                  -- cpu_time_ns values may vary (timing is non-deterministic)
                  -- We verify they exist and are non-negative (can be 0 for very fast evaluations)
                  let cpuTimes = map tsCpuTimeNs samples
                  mapM_
                    ( \t ->
                        assertBool
                          ("cpu_time_ns should be >= 0, got " ++ show t)
                          (t >= 0)
                    )
                    cpuTimes
            ]
        , testGroup
            "UUID Validation - Valid Formats"
            [ testCase "Lowercase UUID v4 format is accepted" do
                execPath <- findEvaluatorExecutable
                withEvaluatorService execPath \handle -> do
                  -- Use a specific lowercase UUID v4
                  let uuidText = "550e8400-e29b-41d4-a716-446655440000"
                  case UUID.fromString uuidText of
                    Nothing -> assertFailure "Test UUID should be valid"
                    Just jobId -> do
                      -- Submit a valid UPLC program with this UUID
                      let program = "(program 1.0.0 (con integer 42))"
                      submitProgram handle jobId program

                      -- Wait for result (should succeed, not produce validation error)
                      path <- waitForResultOrFail handle jobId 5000
                      result <- readResultJsonOrFail path
                      -- Verify program_id matches submitted UUID
                      erProgramId result @?= T.pack uuidText

                      -- Verify status is "success" (not validation error)
                      erStatus result @?= "success"

                      -- Verify we got timing samples (confirms evaluation succeeded)
                      let sampleCount = length (erTimingSamples result)
                      assertBool
                        ("Should have timing samples, got " ++ show sampleCount)
                        (sampleCount >= 10)
            , testCase "Mixed case UUID v4 format is accepted" do
                execPath <- findEvaluatorExecutable
                withEvaluatorService execPath \handle -> do
                  -- Use a mixed case UUID v4
                  let uuidText = "550E8400-E29B-41D4-A716-446655440000"
                  case UUID.fromString uuidText of
                    Nothing -> assertFailure "Test UUID should be valid"
                    Just jobId -> do
                      -- Submit a valid UPLC program with this UUID
                      let program = "(program 1.0.0 (con integer 42))"
                      submitProgram handle jobId program

                      -- Wait for result (should succeed, not produce validation error)
                      path <- waitForResultOrFail handle jobId 5000
                      result <- readResultJsonOrFail path
                      -- Verify status is "success" (not validation error)
                      erStatus result @?= "success"

                      -- Verify we got timing samples
                      let sampleCount = length (erTimingSamples result)
                      assertBool
                        ("Should have timing samples, got " ++ show sampleCount)
                        (sampleCount >= 10)
            , testCase "Multiple randomly generated UUID v4s are accepted" do
                execPath <- findEvaluatorExecutable
                withEvaluatorService execPath \handle -> do
                  -- Generate 3 random UUID v4s and verify all are accepted
                  jobId1 <- UUID.nextRandom
                  jobId2 <- UUID.nextRandom
                  jobId3 <- UUID.nextRandom

                  let program = "(program 1.0.0 (con integer 42))"

                  -- Submit all three programs
                  submitProgram handle jobId1 program
                  submitProgram handle jobId2 program
                  submitProgram handle jobId3 program

                  -- Wait for all results
                  result1Path <- waitForResult handle jobId1 5000
                  result2Path <- waitForResult handle jobId2 5000
                  result3Path <- waitForResult handle jobId3 5000

                  -- Verify all succeeded
                  case (result1Path, result2Path, result3Path) of
                    (Just path1, Just path2, Just path3) -> do
                      -- Parse all results
                      result1Either <- readResultJson path1
                      result2Either <- readResultJson path2
                      result3Either <- readResultJson path3

                      case (result1Either, result2Either, result3Either) of
                        (Right r1, Right r2, Right r3) -> do
                          -- Verify all have success status
                          erStatus r1 @?= "success"
                          erStatus r2 @?= "success"
                          erStatus r3 @?= "success"

                          -- Verify all have correct program IDs
                          erProgramId r1 @?= T.pack (UUID.toString jobId1)
                          erProgramId r2 @?= T.pack (UUID.toString jobId2)
                          erProgramId r3 @?= T.pack (UUID.toString jobId3)

                          -- Verify all have timing samples
                          assertBool "First result should have timing samples" (length (erTimingSamples r1) >= 10)
                          assertBool "Second result should have timing samples" (length (erTimingSamples r2) >= 10)
                          assertBool "Third result should have timing samples" (length (erTimingSamples r3) >= 10)
                        (Left err, _, _) -> assertFailure $ "Failed to parse first result: " ++ err
                        (_, Left err, _) -> assertFailure $ "Failed to parse second result: " ++ err
                        (_, _, Left err) -> assertFailure $ "Failed to parse third result: " ++ err
                    _ -> assertFailure "Timeout waiting for one or more results"
            ]
        , testGroup
            "Processed File Marker"
            [ testCase "Input file is marked as processed and not reprocessed" do
                execPath <- findEvaluatorExecutable
                withEvaluatorService execPath \handle -> do
                  -- Generate a UUID for this job
                  jobId <- UUID.nextRandom

                  -- Submit a valid UPLC program
                  let program = "(program 1.0.0 (con integer 42))"
                  submitProgram handle jobId program

                  -- Wait for result (5 second timeout)
                  path <- waitForResultOrFail handle jobId 5000
                  result <- readResultJsonOrFail path
                  erStatus result @?= "success"

                  -- Verify original file no longer exists
                  let inputFilename = UUID.toString jobId ++ ".uplc.txt"
                      inputPath = shInputDir handle </> inputFilename
                      processedPath = inputPath ++ ".processed"

                  inputExists <- doesFileExist inputPath
                  assertBool "Original input file should not exist" (not inputExists)

                  -- Verify .processed file exists
                  processedExists <- doesFileExist processedPath
                  assertBool "Processed file should exist" processedExists

                  -- Count files in output directory before waiting
                  outputFilesBefore <- listDirectory (shOutputDir handle)
                  let resultFileCountBefore = length outputFilesBefore

                  -- Wait for another poll cycle + processing time (500ms)
                  -- If the service reprocesses the .processed file, it would create
                  -- another result.json (which would fail due to duplicate filename,
                  -- or create an error.json)
                  threadDelay 500000 -- 500ms in microseconds

                  -- Count files in output directory after waiting
                  outputFilesAfter <- listDirectory (shOutputDir handle)
                  let resultFileCountAfter = length outputFilesAfter

                  -- Verify no new files were created (no reprocessing occurred)
                  assertBool
                    ( "File count should not change, was "
                        ++ show resultFileCountBefore
                        ++ ", now "
                        ++ show resultFileCountAfter
                    )
                    (resultFileCountAfter == resultFileCountBefore)
            ]
        , testGroup
            "Concurrent Processing"
            [ testCase "Multiple concurrent job submissions are processed correctly" do
                execPath <- findEvaluatorExecutable
                withEvaluatorService execPath \handle -> do
                  -- Generate 5 unique UUIDs for concurrent jobs
                  jobIds <- sequence [UUID.nextRandom | _ <- [1 .. 5 :: Int]]

                  let program = "(program 1.0.0 (con integer 42))"

                  -- Submit all 5 programs simultaneously
                  mapM_ (\jobId -> submitProgram handle jobId program) jobIds

                  -- Wait for all results (5 second timeout each)
                  paths <- mapM (\jobId -> waitForResultOrFail handle jobId 5000) jobIds
                  results <- mapM readResultJsonOrFail paths
                  -- Verify we got exactly 5 results
                  length results @?= 5

                  -- Verify each result has status "success"
                  mapM_ (\result -> erStatus result @?= "success") results

                  -- Verify each result matches its corresponding UUID (no mix-ups)
                  let resultProgramIds = map erProgramId results
                      expectedIds = map (T.pack . UUID.toString) jobIds
                  mapM_
                    ( \expectedId ->
                        assertBool
                          ( "Expected ID "
                              ++ show expectedId
                              ++ " should be in results"
                          )
                          (expectedId `elem` resultProgramIds)
                    )
                    expectedIds

                  -- Verify no duplicates by checking that all program IDs are unique
                  let uniqueIds = length (nub resultProgramIds)
                      totalIds = length resultProgramIds
                  uniqueIds @?= totalIds

                  -- Verify all results have timing samples
                  mapM_
                    ( \result -> do
                        let sampleCount = length (erTimingSamples result)
                        assertBool
                          ( "Result should have timing samples, got "
                              ++ show sampleCount
                          )
                          (sampleCount >= 10)
                    )
                    results
            ]
        , testGroup
            "Whitespace Handling"
            [ testCase "Program with leading spaces is processed successfully" do
                execPath <- findEvaluatorExecutable
                withEvaluatorService execPath \handle -> do
                  -- Generate a UUID for this job
                  jobId <- UUID.nextRandom

                  -- Submit program with leading spaces
                  let program = "   (program 1.0.0 (con integer 42))"
                  submitProgram handle jobId program

                  -- Wait for result (5 second timeout)
                  path <- waitForResultOrFail handle jobId 5000
                  result <- readResultJsonOrFail path
                  -- Verify status is "success"
                  erStatus result @?= "success"

                  -- Verify we have timing samples
                  let sampleCount = length (erTimingSamples result)
                  assertBool
                    ("Should have timing samples, got " ++ show sampleCount)
                    (sampleCount >= 10)
            , testCase "Program with leading newlines is processed successfully" do
                execPath <- findEvaluatorExecutable
                withEvaluatorService execPath \handle -> do
                  -- Generate a UUID for this job
                  jobId <- UUID.nextRandom

                  -- Submit program with leading newlines
                  let program = "\n\n(program 1.0.0 (con integer 42))"
                  submitProgram handle jobId program

                  -- Wait for result (5 second timeout)
                  path <- waitForResultOrFail handle jobId 5000
                  result <- readResultJsonOrFail path
                  -- Verify status is "success"
                  erStatus result @?= "success"

                  -- Verify we have timing samples
                  let sampleCount = length (erTimingSamples result)
                  assertBool
                    ("Should have timing samples, got " ++ show sampleCount)
                    (sampleCount >= 10)
            , testCase "Program with leading tabs is processed successfully" do
                execPath <- findEvaluatorExecutable
                withEvaluatorService execPath \handle -> do
                  -- Generate a UUID for this job
                  jobId <- UUID.nextRandom

                  -- Submit program with leading tabs
                  let program = "\t(program 1.0.0 (con integer 42))"
                  submitProgram handle jobId program

                  -- Wait for result (5 second timeout)
                  path <- waitForResultOrFail handle jobId 5000
                  result <- readResultJsonOrFail path
                  -- Verify status is "success"
                  erStatus result @?= "success"

                  -- Verify we have timing samples
                  let sampleCount = length (erTimingSamples result)
                  assertBool
                    ("Should have timing samples, got " ++ show sampleCount)
                    (sampleCount >= 10)
            , testCase "Program with mixed whitespace is processed successfully" do
                execPath <- findEvaluatorExecutable
                withEvaluatorService execPath \handle -> do
                  -- Generate a UUID for this job
                  jobId <- UUID.nextRandom

                  -- Submit program with mixed whitespace (spaces, tabs, newlines)
                  let program = " \t\n  \t(program 1.0.0 (con integer 42))"
                  submitProgram handle jobId program

                  -- Wait for result (5 second timeout)
                  path <- waitForResultOrFail handle jobId 5000
                  result <- readResultJsonOrFail path
                  -- Verify status is "success"
                  erStatus result @?= "success"

                  -- Verify we have timing samples
                  let sampleCount = length (erTimingSamples result)
                  assertBool
                    ("Should have timing samples, got " ++ show sampleCount)
                    (sampleCount >= 10)
            ]
        , testGroup
            "SPEC.md Example Programs"
            [ testCase "Example 1: Simple constant (program 1.0.0 (con integer 42))" do
                execPath <- findEvaluatorExecutable
                withEvaluatorService execPath \handle -> do
                  -- Generate a UUID for this job
                  jobId <- UUID.nextRandom

                  -- Submit the example program from SPEC.md
                  let program = "(program 1.0.0 (con integer 42))"
                  submitProgram handle jobId program

                  -- Wait for result (5 second timeout)
                  path <- waitForResultOrFail handle jobId 5000
                  result <- readResultJsonOrFail path
                  -- Verify status is "success"
                  erStatus result @?= "success"

                  -- Verify we have timing samples
                  let sampleCount = length (erTimingSamples result)
                  assertBool
                    ("Should have timing samples, got " ++ show sampleCount)
                    (sampleCount >= 10)
            , testCase "Example 2: Arithmetic with builtins" do
                execPath <- findEvaluatorExecutable
                withEvaluatorService execPath \handle -> do
                  -- Generate a UUID for this job
                  jobId <- UUID.nextRandom

                  -- Submit the arithmetic example from SPEC.md
                  let program =
                        [__i|
                      (program 1.0.0
                        [ [ (builtin addInteger) (con integer 10) ] (con integer 32) ]
                      )
                    |]
                  submitProgram handle jobId program

                  -- Wait for result (5 second timeout)
                  path <- waitForResultOrFail handle jobId 5000
                  result <- readResultJsonOrFail path
                  -- Verify status is "success"
                  erStatus result @?= "success"

                  -- Verify we have timing samples
                  let sampleCount = length (erTimingSamples result)
                  assertBool
                    ("Should have timing samples, got " ++ show sampleCount)
                    (sampleCount >= 10)
            , testCase "Example 3: Lambda application" do
                execPath <- findEvaluatorExecutable
                withEvaluatorService execPath \handle -> do
                  -- Generate a UUID for this job
                  jobId <- UUID.nextRandom

                  -- Submit the lambda application example from SPEC.md
                  let program =
                        [__i|
                      (program 1.0.0
                        [ (lam x [ [ (builtin multiplyInteger) x ] (con integer 2) ])
                          (con integer 21)
                        ]
                      )
                    |]
                  submitProgram handle jobId program

                  -- Wait for result (5 second timeout)
                  path <- waitForResultOrFail handle jobId 5000
                  result <- readResultJsonOrFail path
                  -- Verify status is "success"
                  erStatus result @?= "success"

                  -- Verify we have timing samples
                  let sampleCount = length (erTimingSamples result)
                  assertBool
                    ("Should have timing samples, got " ++ show sampleCount)
                    (sampleCount >= 10)
            , testCase "Example 4: Constructor with version 1.1.0" do
                execPath <- findEvaluatorExecutable
                withEvaluatorService execPath \handle -> do
                  -- Generate a UUID for this job
                  jobId <- UUID.nextRandom

                  -- Submit the constructor example from SPEC.md (version 1.1.0)
                  let program = "(program 1.1.0 (constr 0 (con integer 42) (con bool True)))"
                  submitProgram handle jobId program

                  -- Wait for result (5 second timeout)
                  path <- waitForResultOrFail handle jobId 5000
                  result <- readResultJsonOrFail path
                  -- Verify status is "success"
                  erStatus result @?= "success"

                  -- Verify we have timing samples
                  let sampleCount = length (erTimingSamples result)
                  assertBool
                    ("Should have timing samples, got " ++ show sampleCount)
                    (sampleCount >= 10)
            ]
        ]
    )

{-| Helper function to wait for a file to appear with timeout
Used for non-UUID based filenames where we can't use the standard helpers -}
waitForFileWithTimeout :: FilePath -> Int -> IO (Maybe FilePath)
waitForFileWithTimeout filepath timeoutMs = go 0
  where
    timeoutUs = timeoutMs * 1000
    pollIntervalUs = 50000
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
