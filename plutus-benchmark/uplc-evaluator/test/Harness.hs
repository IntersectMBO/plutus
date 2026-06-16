{-# LANGUAGE RecordWildCards #-}

module Harness
  ( ServiceHandle (..)
  , withEvaluatorService
  , findEvaluatorExecutable
  , stopProcessBounded
  ) where

import Control.Concurrent (threadDelay)
import Control.Exception (bracket)
import System.Directory (findExecutable, removePathForcibly)
import System.Exit (ExitCode (..))
import System.IO (hPutStrLn, stderr)
import System.IO.Temp (createTempDirectory, getCanonicalTemporaryDirectory)
import System.Posix.Signals (sigKILL, signalProcess)
import System.Process
import System.Timeout (timeout)

-- | Handle to a running evaluator service instance
data ServiceHandle = ServiceHandle
  { shProcessHandle :: ProcessHandle
  , shInputDir :: FilePath
  , shOutputDir :: FilePath
  }

{-| Start the uplc-evaluator service with temporary directories

Uses a bracket pattern to ensure the service is stopped and
temporary directories are cleaned up even if tests fail.

The service runs with a short poll interval (100ms) for fast test iteration.

The executable path must be provided - use 'findEvaluatorExecutable' to locate it. -}
withEvaluatorService :: FilePath -> (ServiceHandle -> IO a) -> IO a
withEvaluatorService executablePath action =
  bracket
    startService
    stopService
    action
  where
    startService :: IO ServiceHandle
    startService = do
      -- Create temporary directories
      tmpDir <- getCanonicalTemporaryDirectory
      inputDir <- createTempDirectory tmpDir "uplc-evaluator-input"
      outputDir <- createTempDirectory tmpDir "uplc-evaluator-output"

      hPutStrLn stderr $ "Starting uplc-evaluator service"
      hPutStrLn stderr $ "  Executable: " ++ executablePath
      hPutStrLn stderr $ "  Input dir:  " ++ inputDir
      hPutStrLn stderr $ "  Output dir: " ++ outputDir

      -- Start the service process
      -- Use 100ms poll interval for fast tests
      let processConfig =
            proc
              executablePath
              [ "--input-dir"
              , inputDir
              , "--output-dir"
              , outputDir
              , "--poll-interval"
              , "100"
              ]
      (_, _, _, ph) <- createProcess processConfig

      -- Give the service a moment to start up
      threadDelay 200000 -- 200ms in microseconds
      return
        ServiceHandle
          { shProcessHandle = ph
          , shInputDir = inputDir
          , shOutputDir = outputDir
          }

    stopService :: ServiceHandle -> IO ()
    stopService ServiceHandle {..} = do
      hPutStrLn stderr "Stopping uplc-evaluator service"
      stopProcessBounded gracefulShutdownMicros shProcessHandle

      -- Clean up temporary directories. removePathForcibly tolerates the path
      -- already being gone; an exception here fails the test loudly rather
      -- than hanging.
      hPutStrLn stderr "Cleaning up temporary directories"
      removePathForcibly shInputDir
      removePathForcibly shOutputDir

-- | Grace period (microseconds) between SIGTERM and SIGKILL escalation.
gracefulShutdownMicros :: Int
gracefulShutdownMicros = 5000000 -- 5 seconds

{- Note [Bounded service shutdown]
'waitForProcess' with no timeout blocks until the child exits. If the child
ignores or misses the SIGTERM from 'terminateProcess', that wait never returns,
so teardown — and the whole test run — hangs (plutus-private#2257). We bound
every blocking step instead:

  1. SIGTERM, then wait up to the grace period.
  2. On expiry, re-check the exit code (the wait may have been interrupted just
     as the process exited); if still running, SIGKILL via the raw pid, then
     wait (bounded again) to reap.
  3. If even that expires (a process wedged in uninterruptible disk sleep can
     outlast SIGKILL), give up and leave it: the runner exits moments later and
     init reaps the orphan. Blocking here would be strictly worse.

This runs inside 'bracket''s cleanup, under interruptible 'mask'.
'System.Timeout.timeout' relies on an async exception, and 'waitForProcess'
blocks interruptibly on the threaded RTS (the suite is built with -threaded),
so the timeout fires as intended.
-}

{-| Terminate a process without ever blocking indefinitely.
See Note [Bounded service shutdown]. -}
stopProcessBounded :: Int -> ProcessHandle -> IO ()
stopProcessBounded graceMicros ph = do
  terminateProcess ph
  mExit <- timeout graceMicros (waitForProcess ph)
  case mExit of
    Just exitCode -> reportExit exitCode
    Nothing -> do
      -- The wait may have been interrupted by 'timeout' just as the process
      -- exited, so confirm it is still running before escalating.
      mExited <- getProcessExitCode ph
      case mExited of
        Just exitCode -> reportExit exitCode
        Nothing -> do
          hPutStrLn stderr "Service did not exit after SIGTERM; escalating to SIGKILL"
          mPid <- getPid ph
          mapM_ (signalProcess sigKILL) mPid
          mExit' <- timeout graceMicros (waitForProcess ph)
          case mExit' of
            Just exitCode -> reportExit exitCode
            Nothing -> hPutStrLn stderr "Service survived SIGKILL; abandoning it unreaped"
  where
    reportExit ExitSuccess = hPutStrLn stderr "Service stopped successfully"
    reportExit (ExitFailure code) =
      hPutStrLn stderr $ "Service exited with code: " ++ show code

{-| Find the uplc-evaluator executable

Relies on build-tool-depends to make the executable available in PATH.
This works for both cabal builds (cabal test) and nix builds.
Returns the path if found in PATH, or an error message if not found. -}
findEvaluatorExecutable :: IO FilePath
findEvaluatorExecutable = do
  -- Check if uplc-evaluator is available in PATH
  -- This works because build-tool-depends makes it available for both:
  --   - cabal builds (cabal test adds build-tools to PATH)
  --   - nix builds (nix adds dependencies to PATH)
  pathResult <- findExecutable "uplc-evaluator"
  case pathResult of
    Just path -> return path
    Nothing ->
      error $
        "Could not find uplc-evaluator executable in PATH. "
          ++ "This test suite requires build-tool-depends to make the executable available. "
          ++ "Please ensure you're running tests with 'cabal test' or 'nix build'."
