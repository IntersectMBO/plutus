{-# LANGUAGE TypeOperators #-}

-- See Note [Creation of the Cost Model]
module Main (main) where

import           CriterionExtensions        (criterionMainWith)

import qualified Benchmarks.Bool
import qualified Benchmarks.ByteStrings
import qualified Benchmarks.CryptoAndHashes
import qualified Benchmarks.Data
import qualified Benchmarks.Integers
import qualified Benchmarks.Lists
import qualified Benchmarks.Misc
import qualified Benchmarks.Nops
import qualified Benchmarks.Pairs
import qualified Benchmarks.Strings
import qualified Benchmarks.Tracing
import qualified Benchmarks.Unit

import qualified PlutusCore.DataFilePaths   as DFP

import           Criterion.Main
import           Criterion.Types            as C
import           System.Directory
import           System.Random              (getStdGen)


---------------- Miscellaneous ----------------

{- Creates the .csv file consumed by create-cost-model. The data in this file is
   the time taken for all the builtin operations, as measured by criterion.
   See also Note [Creation of the Cost Model]. -}

{- TODO: Some care is required here regarding the current working directory.  If
   you run this benchmark via `cabal bench` or `stack bench` (but not `cabal
   run`) then the current directory will be `plutus-core`.  If you use nix it'll
   be the current shell directory, so you'll need to run it from `plutus-core`
   (NOT `plutus`, where `default.nix` is).  See SCP-2005. -}

{- Experimentation and examination of implementations suggests that the cost
   models for certain builtins can be re-used for others, and we do this in
   models.R.  Specifically, we re-use the cost models for the functions on the
   left below for the functions on the right as well.  Because of this we don't
   benchmark the functions on the right; the benchmarks take a long time to run,
   so this speeds things up a lot.

   AddInteger:            SubtractInteger
   DivideInteger:         RemainderInteger, QuotientInteger, ModInteger
-}

main :: IO ()
main = do
  gen <- System.Random.getStdGen  -- We use the initial state of gen repeatedly below, but that doesn't matter.
  createDirectoryIfMissing True DFP.costModelDataDir
  csvExists <- doesFileExist DFP.benchingResultsFile
  if csvExists then renameFile DFP.benchingResultsFile DFP.backupBenchingResultsFile else pure ()

  -- Run the nop benchmarks with a large time limit (30 seconds) in an attempt
  -- to get accurate results.  Criterion doesn't expose the functions that would
  -- let us run benchmarks with different time limits and put all the results in
  -- the same file, so we have to use two different CSV files.
{-  criterionMainWith
       True
       (defaultConfig { C.csvFile = Just DFP.benchingResultsFile, C.timeLimit = 30 }) $
       Benchmarks.Nops.makeBenchmarks gen
-}
  criterionMainWith
       False
       (defaultConfig { C.csvFile = Just DFP.benchingResultsFile }) $
 ---           Benchmarks.Unit.makeBenchmarks gen
--        <>  Benchmarks.ByteStrings.makeBenchmarks     gen
          Benchmarks.Tracing.makeBenchmarks         gen
       <> Benchmarks.Misc.makeBenchmarks            gen
       <> Benchmarks.Lists.makeBenchmarks gen
{-            Benchmarks.Strings.makeBenchmarks         gen
        <>  Benchmarks.Integers.makeBenchmarks        gen
        <>  Benchmarks.Bool.makeBenchmarks            gen
        <>  Benchmarks.ByteStrings.makeBenchmarks     gen
        <>  Benchmarks.CryptoAndHashes.makeBenchmarks gen
        <>  Benchmarks.Data.makeBenchmarks            gen
        <>  Benchmarks.Lists.makeBenchmarks           gen
        <>  Benchmarks.Pairs.makeBenchmarks           gen
        <>  Benchmarks.Strings.makeBenchmarks         gen
        <>  Benchmarks.Tracing.makeBenchmarks         gen
        <>  Benchmarks.Unit.makeBenchmarks            gen
        <>  Benchmarks.Misc.makeBenchmarks            gen
-}
