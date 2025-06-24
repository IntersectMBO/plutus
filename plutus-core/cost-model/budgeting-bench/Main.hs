-- See CostModelGeneration.md
{-# OPTIONS_GHC -Wno-deprecations #-}
module Main (main) where

import CriterionExtensions (BenchmarkingPhase (Continue, Start), criterionMainWith)

import Benchmarks.Arrays qualified
import Benchmarks.Bitwise qualified
import Benchmarks.Bool qualified
import Benchmarks.ByteStrings qualified
import Benchmarks.Crypto qualified
import Benchmarks.Data qualified
import Benchmarks.Integers qualified
import Benchmarks.Lists qualified
import Benchmarks.Misc qualified
import Benchmarks.Nops qualified
import Benchmarks.Pairs qualified
import Benchmarks.Strings qualified
import Benchmarks.Tracing qualified
import Benchmarks.Unit qualified

import Criterion.Main
import Criterion.Types as C
import System.Random (RandomGen (next, split), StdGen, getStdGen, mkStdGen)

---------------- Miscellaneous ----------------

{- Creates the .csv file consumed by create-cost-model. The data in this file is
   the time taken for all the builtin operations, as measured by criterion.  See
   also 'CostModelGeneration.md'. -}

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
  -- We use the initial state of gen repeatedly below, but that doesn't matter.
  genEphemeral <- System.Random.getStdGen
  let seed = extractSeed genEphemeral
  putStrLn $ "Using RNG seed: " ++ show seed

  let reusedGen = System.Random.mkStdGen seed

  criterionMainWith
       Start
       defaultConfig $
           Benchmarks.Bitwise.makeBenchmarks
        <> Benchmarks.Bool.makeBenchmarks        reusedGen
        <> Benchmarks.ByteStrings.makeBenchmarks reusedGen
        <> Benchmarks.Crypto.makeBenchmarks      reusedGen
        <> Benchmarks.Data.makeBenchmarks        reusedGen
        <> Benchmarks.Integers.makeBenchmarks    reusedGen
        <> Benchmarks.Lists.makeBenchmarks       reusedGen
        <> Benchmarks.Arrays.makeBenchmarks      reusedGen
        <> Benchmarks.Misc.makeBenchmarks        reusedGen
        <> Benchmarks.Pairs.makeBenchmarks       reusedGen
        <> Benchmarks.Strings.makeBenchmarks     reusedGen
        <> Benchmarks.Tracing.makeBenchmarks     reusedGen
        <> Benchmarks.Unit.makeBenchmarks        reusedGen

  {- Run the nop benchmarks with a large time limit (30 seconds) in an attempt to
     get accurate results. -}
  criterionMainWith
       Continue
       (defaultConfig { C.timeLimit = 30 }) $
       Benchmarks.Nops.makeBenchmarks reusedGen

-- Hacky way to get a reproducible seed from StdGen
extractSeed :: StdGen -> Int
extractSeed gen =
  let (g1, _) = split gen
  in fst (next g1)
