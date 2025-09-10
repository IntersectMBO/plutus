{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE InstanceSigs          #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}

{- | A set of no-op built-in functions used in cost model calibration. Benchmarks
   based on these are used to estimate the overhead of calling a built-in
   function.
-}

module Benchmarks.Nops (makeBenchmarks) where

import Common
import Generators (randBool, randNwords)
import PlutusBenchmark.Common (EvaluationContext)

import PlutusCore
import PlutusCore.Builtin
import PlutusCore.Evaluation.Machine.BuiltinCostModel hiding (BuiltinCostModel)
import PlutusCore.Evaluation.Machine.ExBudgetingDefaults
import PlutusCore.Evaluation.Machine.ExMemoryUsage (ExMemoryUsage)
import PlutusCore.Evaluation.Machine.MachineParameters
import PlutusCore.Pretty
import PlutusPrelude
import UntypedPlutusCore.Evaluation.Machine.Cek

import Criterion.Main (Benchmark, bgroup)

import Data.Ix (Ix)
import System.Random (StdGen)


{- | Arguments to builtins can be treated in several different ways.  Constants of
   built-in types are unlifted to Haskell values automatically and Opaque values
   don't need to be unlifted; unlifting can also be done manually using
   SomeConstant.  Each of these has different costs, and each is used in the
   existing set of builtins (and even for a single function different arguments
   may be handled in different ways, as in ifThenElse where the first argument
   is a built-in Bool value but the last two are Opaque PLC values).  These
   benchmarks are intended to give some idea of how much overhead each of these
   processses incurs; the results are used in the R code that we use to fit cost
   models. There's also a cost for lifting the result of a builtin call back to
   a Plutus value, and that's included in the benchmark results as well. -}

---------------- Benchmarks ----------------

{- We want the benchmark results to reflect only the time taken to evaluate a
   builtin, not the startup costs of the CEK machine or the overhead incurred
   while collecting the arguments (applyEvaluate/ forceEvaluate etc).  We
   benchmark the no-op builtins and in the R code we subtract the costs of those
   from the time recorded for the real builtins.  Experiments suggest that the
   time taken to evaluate these doesn't depend on the types or the sizes of the
   arguments, so we just use functions which consume a number of arguments and
   return a constant. -}

-- There seems to be quite a lot of variation in repeated runs of these benchmarks.
-- In general we have Built-in > SomeConstant > Opaque though.

{- | `benchNopN` generates N random inputs and makes a benchmark measuring how
   long it takes the given function to run with those arguments.  Take care that
   N matches the number of arguments of the function or else you'll be
   benchmarking an overapplication (which will fail) or a partial application
   (which will succeed, but would give misleading results).  For example, only
   apply benchNop5 to a Nop5 function, not to something like Nop6i or Nop2o.
 -}

benchNop1
    :: (ExMemoryUsage a, DefaultUni `HasTermLevel` a, NFData a)
    => EvaluationContext
    -> DefaultFun
    -> (StdGen -> (a, StdGen))
    -> StdGen
    -> Benchmark
benchNop1 evalCtx nop rand gen =
    let (x,_) = rand gen
    in bgroup (show nop) [benchWithCtx evalCtx (showMemoryUsage x) $ mkApp1 nop [] x]

benchNop2
    :: (ExMemoryUsage a, DefaultUni `HasTermLevel` a, NFData a)
    => EvaluationContext
    -> DefaultFun
    -> (StdGen -> (a, StdGen))
    -> StdGen
    -> Benchmark
benchNop2 evalCtx nop rand gen =
    let (x,gen1) = rand gen
        (y,_)    = rand gen1
    in bgroup (show nop)
           [bgroup (showMemoryUsage x)
            [benchWithCtx evalCtx (showMemoryUsage y) $ mkApp2 nop [] x y]
           ]

benchNop3
    :: (ExMemoryUsage a, DefaultUni `HasTermLevel` a, NFData a)
    => EvaluationContext
    -> DefaultFun
    -> (StdGen -> (a, StdGen))
    -> StdGen
    -> Benchmark
benchNop3 evalCtx nop rand gen =
    let (x,gen1) = rand gen
        (y,gen2) = rand gen1
        (z,_)    = rand gen2
    in bgroup (show nop)
           [bgroup (showMemoryUsage x)
            [bgroup (showMemoryUsage y)
             [benchWithCtx evalCtx (showMemoryUsage z) $ mkApp3 nop [] x y z]
            ]
           ]

benchNop4
    :: (ExMemoryUsage a, DefaultUni `HasTermLevel` a, NFData a)
    => EvaluationContext
    -> DefaultFun
    -> (StdGen -> (a, StdGen))
    -> StdGen
    -> Benchmark
benchNop4 evalCtx nop rand gen =
    let (x,gen1) = rand gen
        (y,gen2) = rand gen1
        (z,gen3) = rand gen2
        (t,_)    = rand gen3
    in bgroup (show nop)
           [bgroup (showMemoryUsage x)
            [bgroup (showMemoryUsage y)
             [bgroup (showMemoryUsage z)
              [benchWithCtx evalCtx (showMemoryUsage t) $ mkApp4 nop [] x y z t]
             ]
            ]
           ]

benchNop5
    :: (ExMemoryUsage a, DefaultUni `HasTermLevel` a, NFData a)
    => EvaluationContext
    -> DefaultFun
    -> (StdGen -> (a, StdGen))
    -> StdGen
    -> Benchmark
benchNop5 evalCtx nop rand gen =
    let (x,gen1) = rand gen
        (y,gen2) = rand gen1
        (z,gen3) = rand gen2
        (t,gen4) = rand gen3
        (u,_)    = rand gen4
    in bgroup (show nop)
           [bgroup (showMemoryUsage x)
            [bgroup (showMemoryUsage y)
             [bgroup (showMemoryUsage z)
              [bgroup (showMemoryUsage t)
               [benchWithCtx evalCtx (showMemoryUsage u) $ mkApp5 nop [] x y z t u]
              ]
             ]
            ]
           ]

benchNop6
    :: (ExMemoryUsage a, DefaultUni `HasTermLevel` a, NFData a)
    => EvaluationContext
    -> DefaultFun
    -> (StdGen -> (a, StdGen))
    -> StdGen
    -> Benchmark
benchNop6 evalCtx nop rand gen =
    let (x,gen1) = rand gen
        (y,gen2) = rand gen1
        (z,gen3) = rand gen2
        (t,gen4) = rand gen3
        (u,gen5) = rand gen4
        (v,_)    = rand gen5
    in bgroup (show nop)
           [bgroup (showMemoryUsage x)
            [bgroup (showMemoryUsage y)
             [bgroup (showMemoryUsage z)
              [bgroup (showMemoryUsage t)
               [bgroup (showMemoryUsage u)
                [benchWithCtx evalCtx (showMemoryUsage v) $ mkApp6 nop [] x y z t u v]
               ]
              ]
             ]
            ]
           ]


-- | The actual benchmarks
makeBenchmarks :: EvaluationContext -> StdGen -> [Benchmark]
makeBenchmarks evalCtx gen =
    mkBMs mkBmI (Nop1o, Nop2o, Nop3o, Nop4o, Nop5o, Nop6o)
   -- The subsidiary functions below make it a lot easier to see that we're
   -- benchmarking the right things with the right benchmarking functions.
   -- Maybe we could use some TH instead.
    where mkBMs mkBM (nop1, nop2, nop3, nop4, nop5, nop6) =
              [ mkBM (benchNop1 evalCtx) nop1
              , mkBM (benchNop2 evalCtx) nop2
              , mkBM (benchNop3 evalCtx) nop3
              , mkBM (benchNop4 evalCtx) nop4
              , mkBM (benchNop5 evalCtx) nop5
              , mkBM (benchNop6 evalCtx) nop6 ]
          mkBmB benchfn nop = benchfn evalCtx nop randBool gen
          mkBmI benchfn nop = benchfn nop (randNwords 1)  gen
          -- Benchmark using Integer inputs with memory usage 1
