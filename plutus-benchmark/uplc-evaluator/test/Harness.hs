{-# LANGUAGE RecordWildCards #-}

module Harness
  ( ServiceHandle (..)
  , withEvaluatorService
  , findEvaluatorExecutable
  ) where

import Control.Concurrent (threadDelay)
import Control.Exception (bracket)
import System.Directory (doesFileExist, getCurrentDirectory, removeDirectoryRecursive)
import System.Exit (ExitCode (..))
import System.FilePath ((</>))
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

Searches in common locations where cabal places built executables.
Returns the path if found, or an error message if not found. -}
findEvaluatorExecutable :: IO FilePath
findEvaluatorExecutable = do
  -- Get current directory to build absolute paths
  -- Tests may run from plutus-benchmark subdirectory, so check both
  cwd <- getCurrentDirectory

  -- Try the standard cabal dist-newstyle locations
  let relativeCandidates =
        [ "dist-newstyle/build/x86_64-linux/ghc-9.6.7/plutus-benchmark-0.1.0.0/x/uplc-evaluator/build/uplc-evaluator/uplc-evaluator"
        , "dist-newstyle/build/x86_64-linux/ghc-9.8.4/plutus-benchmark-0.1.0.0/x/uplc-evaluator/build/uplc-evaluator/uplc-evaluator"
        , "dist-newstyle/build/x86_64-linux/ghc-9.10.1/plutus-benchmark-0.1.0.0/x/uplc-evaluator/build/uplc-evaluator/uplc-evaluator"
        , -- Also try with aarch64 for Apple Silicon Macs
          "dist-newstyle/build/aarch64-osx/ghc-9.6.7/plutus-benchmark-0.1.0.0/x/uplc-evaluator/build/uplc-evaluator/uplc-evaluator"
        , "dist-newstyle/build/aarch64-osx/ghc-9.8.4/plutus-benchmark-0.1.0.0/x/uplc-evaluator/build/uplc-evaluator/uplc-evaluator"
        , "dist-newstyle/build/aarch64-osx/ghc-9.10.1/plutus-benchmark-0.1.0.0/x/uplc-evaluator/build/uplc-evaluator/uplc-evaluator"
        ]
      -- Convert to absolute paths from both current directory and parent directory
      candidates = map (cwd </>) relativeCandidates ++ map ((cwd </> "..") </>) relativeCandidates

  -- Find first existing candidate
  findFirst candidates
  where
    findFirst :: [FilePath] -> IO FilePath
    findFirst [] =
      error $
        "Could not find uplc-evaluator executable. "
          ++ "Please build it first with: cabal build uplc-evaluator"
    findFirst (path : rest) = do
      exists <- doesFileExist path
      if exists
        then return path
        else findFirst rest
