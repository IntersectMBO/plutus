{-# LANGUAGE LambdaCase #-}

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
import System.Environment (getProgName)
import System.Exit (ExitCode (..), exitWith)


{- | A modified version of Criterion's 'defaultMainWith' function. We want to be
   able to run different benchmarks with different time limits, but that doesn't
   work with the original version because the relevant function appends output
   to a CSV file but writes a header into the file every time it's called.  This
   adds an option to stop it doing that so we only get one header (at the top,
   where it belongs). -}

criterionMainWith :: Bool ->  Config -> [Benchmark] -> IO ()
criterionMainWith writeHeader defCfg bs =
  execParser (describe defCfg) >>=
     \case
      List -> mapM_ putStrLn . sort . concatMap benchNames $ bs
      Version -> putStrLn versionInfo
      RunIters cfg iters matchType benches ->
          do
            shouldRun <- selectBenches matchType benches bsgroup
            withConfig cfg $ runFixedIters iters shouldRun bsgroup
      Run cfg matchType benches ->
          do
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
