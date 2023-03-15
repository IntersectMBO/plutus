-- See CostModelGeneration.md
module Main (main) where

import CriterionExtensions (BenchmarkingPhase (Continue, Start), criterionMainWith)

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
import System.Random (getStdGen)

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
  gen <- System.Random.getStdGen

  criterionMainWith
       Start
       defaultConfig $
            Benchmarks.Bool.makeBenchmarks        gen
        <>  Benchmarks.ByteStrings.makeBenchmarks gen
        <>  Benchmarks.Crypto.makeBenchmarks      gen
        <>  Benchmarks.Data.makeBenchmarks        gen
        <>  Benchmarks.Integers.makeBenchmarks    gen
        <>  Benchmarks.Lists.makeBenchmarks       gen
        <>  Benchmarks.Misc.makeBenchmarks        gen
        <>  Benchmarks.Pairs.makeBenchmarks       gen
        <>  Benchmarks.Strings.makeBenchmarks     gen
        <>  Benchmarks.Tracing.makeBenchmarks     gen
        <>  Benchmarks.Unit.makeBenchmarks        gen

  {- Run the nop benchmarks with a large time limit (30 seconds) in an attempt to
     get accurate results. -}
  -- FIXME: this doesn't quite work.  If you specify a benchmark name on the
  -- command line and it's in the first group then it'll run but you'll get an
  -- error when the argument gets passed to the nop benchmarks below (but the
  -- data will still be generated and saved in benching.csv).

  criterionMainWith
       Continue
       (defaultConfig { C.timeLimit = 30 }) $
       Benchmarks.Nops.makeBenchmarks gen
