{-# LANGUAGE TypeOperators #-}

-- See Note [Creation of the Cost Model]
module Main (main) where

import CriterionExtensions (criterionMainWith)

import Benchmarks.Bool qualified
import Benchmarks.ByteStrings qualified
import Benchmarks.CryptoAndHashes qualified
import Benchmarks.Data qualified
import Benchmarks.Integers qualified
import Benchmarks.Lists qualified
import Benchmarks.Misc qualified
import Benchmarks.Nops qualified
import Benchmarks.Pairs qualified
import Benchmarks.Strings qualified
import Benchmarks.Tracing qualified
import Benchmarks.Unit qualified

import PlutusCore.DataFilePaths qualified as DFP

import Criterion.Main
import Criterion.Types as C
import System.Directory
import System.Random (getStdGen)


---------------- Miscellaneous ----------------

{- Creates the .csv file consumed by create-cost-model. The data in this file is
   the time taken for all the builtin operations, as measured by criterion.  See
   also Note [Creation of the Cost Model]. -}

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

  criterionMainWith
       True
       (defaultConfig { C.csvFile = Just DFP.benchingResultsFile, C.timeLimit = 30 }) $
       Benchmarks.Nops.makeBenchmarks gen
