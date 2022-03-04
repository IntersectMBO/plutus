{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE LambdaCase   #-}

module CriterionExtensions (criterionMainWith) where

import Control.Monad (unless)
import Control.Monad.Trans (liftIO)
import Criterion.IO.Printf (printError, writeCsv)
import Criterion.Internal (runAndAnalyse, runFixedIters)
import Criterion.Main (makeMatcher)
import Criterion.Main.Options (MatchType (..), Mode (..), describe, versionInfo)
import Criterion.Measurement (initializeTime)
import Criterion.Monad (withConfig)
import Criterion.Types

import Data.List (sort)
import Options.Applicative (execParser)
import System.Directory (doesFileExist, renameFile)
import System.Environment (getProgName)
import System.Exit (ExitCode (..), exitWith)
import System.FilePath ((<.>))


{- | We require the user to specify a CSV output file: without this, Criterion
   won't save the output that we really need.  We previously wrote the data to a
   fixed location, but that was too inflexible. If the output file already
   exists then we move it to a backup file because by default Criterion will
   just append data to the existing file (including a new header).
-}
checkCsvSet :: Config -> IO ()
checkCsvSet cfg =
    case csvFile cfg of
      Nothing -> do
        prog <- getProgName
        putStrLn ""
        putStrLn "ERROR: a CSV output file must be specified for the benchmarking results."
        putStrLn "Use either "
        putStrLn ""
        putStrLn $ "   cabal run " ++ prog ++ " -- --csv <file>"
        putStrLn ""
        putStrLn "or"
        putStrLn ""
        putStrLn $ "   cabal bench " ++ prog ++ " --benchmark-option \"--csv <file>\""
        putStrLn ""
        putStrLn "With `cabal run` the CSV file location will be relative to the current shell directory,"
        putStrLn "with `cabal bench`, it will be relative to the plutus-core directory."
        putStrLn ""
        exitWith $ ExitFailure 5
      Just file  -> do
        csvExists <- doesFileExist file
        if csvExists
        then renameFile file (file <.> "backup")
        else pure ()

{- | A modified version of Criterion's 'defaultMainWith' function. We want to be
   able to run different benchmarks with different time limits, but that doesn't
   work with the original version because the relevant function appends output
   to a CSV file but writes a header into the file every time it's called.  This
   adds an option to stop it doing that so we only get one header (at the top,
   where it belongs).  This also calls `checkCsvSet` to make sure that a CSV
   output file has been specified. -}
criterionMainWith :: Bool ->  Config -> [Benchmark] -> IO ()
criterionMainWith writeHeader defCfg bs =
  execParser (describe defCfg) >>=
     \case
      List -> mapM_ putStrLn . sort . concatMap benchNames $ bs
      Version -> putStrLn versionInfo
      RunIters cfg iters matchType benches ->
          do
            () <- checkCsvSet cfg
            shouldRun <- selectBenches matchType benches bsgroup
            withConfig cfg $ runFixedIters iters shouldRun bsgroup
      Run cfg matchType benches ->
          do
            () <- checkCsvSet cfg
            shouldRun <- selectBenches matchType benches bsgroup
            withConfig cfg $ do
              if writeHeader
              then  writeCsv ("Name","Mean","MeanLB","MeanUB","Stddev","StddevLB", "StddevUB")
              else return ()
              liftIO initializeTime
              runAndAnalyse shouldRun bsgroup
      where bsgroup = BenchGroup "" bs

selectBenches :: MatchType -> [String] -> Benchmark -> IO (String -> Bool)
selectBenches matchType benches bsgroup = do
  toRun <- either parseError return . makeMatcher matchType $ benches
  unless (null benches || any toRun (benchNames bsgroup)) $
    parseError "none of the specified names matches a benchmark"
  return toRun

parseError :: String -> IO a
parseError msg = do
  _ <- printError "Error: %s\n" msg
  _ <- printError "Run \"%s --help\" for usage information\n" =<< getProgName
  exitWith (ExitFailure 64)
