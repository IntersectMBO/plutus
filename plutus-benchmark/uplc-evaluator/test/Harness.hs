{-# LANGUAGE RecordWildCards #-}

module Harness
  ( ServiceHandle (..)
  , withEvaluatorService
  , findEvaluatorExecutable
  ) where

import Control.Concurrent (threadDelay)
import Control.Exception (bracket)
import System.Directory (findExecutable, removeDirectoryRecursive)
import System.Exit (ExitCode (..))
import System.IO (hPutStrLn, stderr)
import System.IO.Temp (createTempDirectory, getCanonicalTemporaryDirectory)
import System.Process

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

      -- Send SIGTERM for graceful shutdown
      terminateProcess shProcessHandle

      -- Wait for process to exit
      exitCode <- waitForProcess shProcessHandle
      case exitCode of
        ExitSuccess -> hPutStrLn stderr "Service stopped successfully"
        ExitFailure code -> hPutStrLn stderr $ "Service exited with code: " ++ show code

      -- Clean up temporary directories
      hPutStrLn stderr "Cleaning up temporary directories"
      removeDirectoryRecursive shInputDir
      removeDirectoryRecursive shOutputDir

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
