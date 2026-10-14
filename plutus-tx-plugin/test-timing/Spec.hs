-- | Tests for 'timeStage': forcing, output, and exceptions.
module Main (main) where

import PlutusTx.Plugin.Timing (timeStage)

import Control.DeepSeq (rnf)
import Control.Exception (SomeException, bracket, evaluate, finally, try)
import Data.IORef (modifyIORef', newIORef, readIORef)
import GHC.IO.Handle (hDuplicate, hDuplicateTo)
import System.IO (SeekMode (AbsoluteSeek), hClose, hFlush, hGetContents, hSeek, stderr)
import System.IO.Temp (withSystemTempFile)
import Test.Tasty (defaultMain, localOption, testGroup)
import Test.Tasty.HUnit (Assertion, assertBool, assertFailure, testCase, (@?=))
import Test.Tasty.Runners (NumThreads (..))
import Text.Read (readMaybe)

-- | Run serially because stderr redirection is process-wide.
main :: IO ()
main =
  defaultMain $
    localOption (NumThreads 1) $
      testGroup
        "Stage timings"
        [ testCase "disabled timing does not force the result or emit output" $ do
            (result, output) <-
              captureStderr $
                timeStage False True "test" "disabled" rnf (pure (error "deferred" :: Int))
            output @?= ""
            assertThrows (evaluate result)
        , testCase "disabled timing does not evaluate the forcing function" $ do
            (result, output) <-
              captureStderr $
                timeStage False True "test" "disabled" (error "unused forcing function") (pure (42 :: Int))
            result @?= 42
            output @?= ""
        , testCase "enabled timing preserves the result and runs the action once" $ do
            counter <- newIORef (0 :: Int)
            (result, output) <- captureStderr $ timeStage True True "test" "successful" rnf $ do
              modifyIORef' counter (+ 1)
              pure [1 :: Int, 2]
            result @?= [1, 2]
            readIORef counter >>= (@?= 1)
            case words output of
              [prefix, scope, stage, wall, cpu] -> do
                prefix @?= "PLINTH_TIMING"
                scope @?= "test"
                stage @?= "successful"
                assertBool "nonnegative wall nanoseconds" (maybe False (>= 0) (readMaybe wall :: Maybe Integer))
                assertBool "nonnegative CPU picoseconds" (maybe False (>= 0) (readMaybe cpu :: Maybe Integer))
                output @?= "PLINTH_TIMING\ttest\tsuccessful\t" <> wall <> "\t" <> cpu <> "\n"
              _ -> assertFailure ("Unexpected timing output: " <> output)
        , testCase "enabled timing forces a lazy tail before reporting success" $ do
            (_, output) <-
              captureStderr $
                assertThrows $
                  timeStage True True "test" "failed" rnf (pure [1 :: Int, error "lazy tail"])
            output @?= ""
        , testCase "action failures are propagated without a success record" $ do
            (_, output) <-
              captureStderr $
                assertThrows $
                  timeStage True True "test" "failed" rnf (evaluate (error "failed action" :: Int))
            output @?= ""
        , testCase "non-forcing timing preserves a lazy result and emits one record" $ do
            counter <- newIORef (0 :: Int)
            (result, output) <- captureStderr $ timeStage True False "test" "lazy" rnf $ do
              modifyIORef' counter (+ 1)
              pure (error "deferred" :: Int)
            readIORef counter >>= (@?= 1)
            length (lines output) @?= 1
            take 3 (words output) @?= ["PLINTH_TIMING", "test", "lazy"]
            assertThrows (evaluate result)
        , testCase "non-forcing timing does not evaluate the forcing function" $ do
            (result, output) <-
              captureStderr $
                timeStage True False "test" "lazy" (error "unused forcing function") (pure (42 :: Int))
            result @?= 42
            length (lines output) @?= 1
        , testCase "non-forcing timing propagates action failures without a record" $ do
            (_, output) <-
              captureStderr $
                assertThrows $
                  timeStage True False "test" "failed" rnf (evaluate (error "failed action" :: Int))
            output @?= ""
        ]

-- | Assert that the action throws something.
assertThrows :: IO result -> Assertion
assertThrows action = do
  outcome <- try (action >> pure ()) :: IO (Either SomeException ())
  case outcome of
    Left _ -> pure ()
    Right () -> assertFailure "Expected an exception"

-- | Capture stderr during the action, restoring it even if the action throws.
captureStderr :: IO result -> IO (result, String)
captureStderr action = withSystemTempFile "plinth-timings" $ \_ captured ->
  bracket (hDuplicate stderr) hClose $ \original -> do
    result <-
      (hDuplicateTo captured stderr >> action)
        `finally` (hFlush stderr >> hDuplicateTo original stderr)
    hSeek captured AbsoluteSeek 0
    output <- hGetContents captured
    evaluate (rnf output)
    pure (result, output)
