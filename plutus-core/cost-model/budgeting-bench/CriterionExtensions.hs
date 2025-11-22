{-# LANGUAGE LambdaCase #-}

module CriterionExtensions (criterionMainWith, BenchmarkingPhase (..)) where

import Control.Monad.Trans (liftIO)
import Criterion.IO.Printf (printError, writeCsv)
import Criterion.Internal (runAndAnalyse, runFixedIters)
import Criterion.Main (makeMatcher)
import Criterion.Main.Options (MatchType (..), Mode (..), describe, versionInfo)
import Criterion.Measurement (initializeTime)
import Criterion.Monad (Criterion, withConfig)
import Criterion.Types

import Data.List (sort)
import Data.Time.Clock (getCurrentTime)
import Options.Applicative (execParser)
import System.Directory (doesFileExist, renameFile)
import System.Environment (getProgName)
import System.Exit (exitFailure)
import System.FilePath ((<.>))
import System.IO (hPutStrLn, stderr)

{-| The first time we call criterionMainWith we want to check that the CSV file
   exists and if it does we make a backup and open a new version, writing a
   header to the it.  If we call criterionMainWith again then we just want to
   append to the existing file: this type tells us which of these things we want
   to do. -}
data BenchmarkingPhase = Start | Continue

{-| We require the user to specify a CSV output file: without this, Criterion
   won't save the output that we really need.  We previously wrote the data to a
   fixed location, but that was too inflexible. If the phase is Start and the
   output file already exists then we move it to a backup file because by
   default Criterion will just append data to the existing file (including a new
   header). -}
initCsvFile :: BenchmarkingPhase -> Config -> Criterion ()
initCsvFile phase cfg =
  let putStrLnErr = hPutStrLn stderr
   in case csvFile cfg of
        Nothing ->
          liftIO $ do
            prog <- getProgName
            putStrLnErr ""
            putStrLnErr "ERROR: a CSV output file must be specified for the benchmarking results."
            putStrLnErr "Use"
            putStrLnErr ""
            putStrLnErr $ "   cabal run " ++ prog ++ " -- --csv <file>"
            putStrLnErr ""
            putStrLnErr "The CSV file location will be relative to the current shell directory."
            exitFailure
        Just file -> do
          case phase of
            Start -> do
              csvExists <- liftIO $ doesFileExist file
              if csvExists
                then liftIO $ renameFile file (file <.> "backup")
                else pure ()
              time <- liftIO getCurrentTime
              liftIO $ appendFile file $ "# Plutus Core cost model benchmark results\n"
              liftIO $ appendFile file $ "# Started at " ++ show time ++ "\n"
              writeCsv ("benchmark", "t", "t.mean.lb", "t.mean.ub", "t.sd", "t.sd.lb", "t.sd.ub")
            -- Criterion will append output to the CSV file specified in `cfg`.
            Continue -> pure ()

{-| A modified version of Criterion's 'defaultMainWith' function. We want to be
   able to run different benchmarks with different time limits, but that doesn't
   work with the original version because the relevant function appends output
   to a CSV file but writes a header into the file every time it's called.  This
   adds an option to stop it doing that so we only get one header (at the top,
   where it belongs).  This also calls `initCsvFile` to make sure that a CSV
   output file has been specified. -}

-- TODO: bypass Criterion's command line parser altogether.
criterionMainWith :: BenchmarkingPhase -> Config -> [Benchmark] -> IO ()
criterionMainWith phase defCfg bs =
  execParser (describe defCfg)
    >>= \case
      List -> mapM_ putStrLn . sort . concatMap benchNames $ bs
      Version -> putStrLn versionInfo
      RunIters cfg iters matchType benches ->
        withConfig cfg $ do
          () <- initCsvFile phase cfg
          shouldRun <- liftIO $ selectBenches matchType benches
          runFixedIters iters shouldRun bsgroup
      Run cfg matchType benches ->
        withConfig cfg $ do
          () <- initCsvFile phase cfg
          shouldRun <- liftIO $ selectBenches matchType benches
          liftIO initializeTime
          runAndAnalyse shouldRun bsgroup
  where
    bsgroup = BenchGroup "" bs

-- Select the benchmarks to be run.  If a pattern is specified on the command
-- line then only the matching benchmarks will be run.  If there are no matching
-- benchmarks then the command will stil succeed (with no error or warning), but
-- nothing will be benchmarked.
selectBenches :: MatchType -> [String] -> IO (String -> Bool)
selectBenches matchType benches = do
  toRun <- either parseError return . makeMatcher matchType $ benches
  return toRun

parseError :: String -> IO a
parseError msg = do
  _ <- printError "Error: %s\n" msg
  _ <- printError "Run \"%s --help\" for usage information\n" =<< getProgName
  exitFailure
