{-# LANGUAGE LambdaCase #-}

-- | Tests for 'timeStage': forcing, output, and exceptions.
module Main (main) where

import PlutusTx.Plugin.Timing (timeStage, timingsEnabled)

import Control.DeepSeq (rnf)
import Control.Exception (SomeException, evaluate, try)
import Data.IORef (modifyIORef', newIORef, readIORef)
import Data.List (isPrefixOf)
import GHC.Driver.Flags (DumpFlag (Opt_D_dump_timings))
import GHC.Utils.Logger
  ( LogFlags (log_verbosity)
  , Logger
  , initLogger
  , log_set_dopt
  , pushDumpHook
  , pushLogHook
  , updateLogFlags
  )
import GHC.Utils.Outputable (defaultSDocContext, renderWithContext)
import Test.Tasty (defaultMain, testGroup)
import Test.Tasty.HUnit (Assertion, assertBool, assertFailure, testCase, (@?=))

main :: IO ()
main =
  defaultMain $
    testGroup
      "Stage timings"
      [ testCase "timings are off without -ddump-timings or -v2" $ do
          (logger, _) <- captureTimings id
          timingsEnabled logger @?= False
      , testCase "-v2 turns timings on" $ do
          (logger, _) <- captureTimings (\flags -> flags {log_verbosity = 2})
          timingsEnabled logger @?= True
      , testCase "disabled timing does not force the result or emit output" $ do
          (logger, records) <- captureTimings id
          result <- timeStage logger True "test" "disabled" rnf (pure (error "deferred" :: Int))
          records >>= (@?= [])
          assertThrows (evaluate result)
      , testCase "disabled timing does not evaluate the forcing function" $ do
          (logger, records) <- captureTimings id
          result <- timeStage logger True "test" "disabled" (error "unused") (pure (42 :: Int))
          result @?= 42
          records >>= (@?= [])
      , testCase "enabled timing preserves the result and runs the action once" $ do
          (logger, records) <- captureTimings dumpTimings
          counter <- newIORef (0 :: Int)
          result <- timeStage logger True "test" "successful" rnf $ do
            modifyIORef' counter (+ 1)
            pure [1 :: Int, 2]
          result @?= [1, 2]
          readIORef counter >>= (@?= 1)
          records >>= \case
            [record] ->
              assertBool record ("Plinth successful [test]: alloc=" `isPrefixOf` record)
            other -> assertFailure ("Expected one record, got " <> show other)
      , testCase "forcing timing forces a lazy tail before reporting success" $ do
          (logger, records) <- captureTimings dumpTimings
          assertThrows $
            timeStage logger True "test" "failed" rnf (pure [1 :: Int, error "lazy tail"])
          records >>= (@?= [])
      , testCase "action failures are propagated without a record" $ do
          (logger, records) <- captureTimings dumpTimings
          assertThrows $
            timeStage logger True "test" "failed" rnf (evaluate (error "failed action" :: Int))
          records >>= (@?= [])
      , testCase "non-forcing timing leaves a lazy tail and emits one record" $ do
          (logger, records) <- captureTimings dumpTimings
          result <- timeStage logger False "test" "lazy" rnf (pure [1 :: Int, error "lazy tail"])
          fmap length records >>= (@?= 1)
          assertThrows (evaluate (rnf result))
      , testCase "non-forcing timing does not evaluate the forcing function" $ do
          (logger, records) <- captureTimings dumpTimings
          result <- timeStage logger False "test" "lazy" (error "unused") (pure (42 :: Int))
          result @?= 42
          fmap length records >>= (@?= 1)
      ]

-- | Turn on @-ddump-timings@.
dumpTimings :: LogFlags -> LogFlags
dumpTimings = log_set_dopt Opt_D_dump_timings

{-| A logger with the given flags whose dumps are collected rather than printed, and an
action that returns the collected dumps in order. Other log messages are discarded. -}
captureTimings :: (LogFlags -> LogFlags) -> IO (Logger, IO [String])
captureTimings setFlags = do
  dumps <- newIORef []
  base <- initLogger
  let collect _ _ _ _ _ doc = modifyIORef' dumps (renderWithContext defaultSDocContext doc :)
      logger =
        pushDumpHook (const collect) $
          pushLogHook (const (\_ _ _ _ -> pure ())) $
            updateLogFlags base setFlags
  pure (logger, reverse <$> readIORef dumps)

-- | Assert that the action throws something.
assertThrows :: IO result -> Assertion
assertThrows action = do
  outcome <- try (action >> pure ()) :: IO (Either SomeException ())
  case outcome of
    Left _ -> pure ()
    Right () -> assertFailure "Expected an exception"
