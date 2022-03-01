{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE InstanceSigs          #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}

{- | A set of no-op built-in functions used in cost model calibration. Benchmarks
   based on these are used to estimate the overhead of calling a built-in
   function.
-}

module Benchmarks.Nops (makeBenchmarks) where

import Common
import Generators (randNwords)

import PlutusCore
import PlutusCore.Builtin
import PlutusCore.Evaluation.Machine.BuiltinCostModel hiding (BuiltinCostModel)
import PlutusCore.Evaluation.Machine.MachineParameters
import PlutusCore.Pretty
import UntypedPlutusCore.Evaluation.Machine.Cek

import Control.DeepSeq (NFData)
import Criterion.Main
import Data.Char (toLower)
import Data.Ix (Ix)
import GHC.Generics (Generic)
import System.Random (StdGen)

data NopFuns
    = Nop1
    | Nop2
    | Nop3
    | Nop4
    | Nop5
    | Nop6
    deriving (Show, Eq, Ord, Enum, Bounded, Generic, NFData, Ix, PrettyBy PrettyConfigPlc)

instance Pretty NopFuns where
    pretty fun = pretty $ case show fun of
        ""    -> ""
        c : s -> toLower c : s

data NopCostModel =
    NopCostModel
    { paramNop1 :: CostingFun ModelOneArgument
    , paramNop2 :: CostingFun ModelTwoArguments
    , paramNop3 :: CostingFun ModelThreeArguments
    , paramNop4 :: CostingFun ModelFourArguments
    , paramNop5 :: CostingFun ModelFiveArguments
    , paramNop6 :: CostingFun ModelSixArguments
    }

{- | A fake cost model for nops.  This is just to make sure that the overhead of
   calling the costing function is included, so the precise contents don't
   matter as long as the basic form is correct (and benchmarks suggest that nops
   indeed have constant costs). -}
nopCostModel :: NopCostModel
nopCostModel =
    NopCostModel
    {
      paramNop1 = CostingFun
                  (ModelOneArgumentConstantCost 1000000)
                  (ModelOneArgumentConstantCost 100)
    , paramNop2 = CostingFun
                  (ModelTwoArgumentsConstantCost 1250000)
                  (ModelTwoArgumentsConstantCost 200)
    , paramNop3 = CostingFun
                  (ModelThreeArgumentsConstantCost 1500000)
                  (ModelThreeArgumentsConstantCost 300)
    , paramNop4 = CostingFun
                  (ModelFourArgumentsConstantCost 1750000)
                  (ModelFourArgumentsConstantCost 400)
    , paramNop5 = CostingFun
                  (ModelFiveArgumentsConstantCost 2000000)
                  (ModelFiveArgumentsConstantCost 500)
    , paramNop6 = CostingFun
                  (ModelSixArgumentsConstantCost 2250000)
                  (ModelSixArgumentsConstantCost 600)
    }

nopCostParameters :: MachineParameters CekMachineCosts CekValue DefaultUni NopFuns
nopCostParameters = mkMachineParameters $ CostModel defaultCekMachineCosts nopCostModel

{- | The meanings of the builtins.  Each one takes a number of integer arguments
   and returns an integer without doing any other work.  We could have used
   units instead of integers, but using integers makes it possible to check that
   the cost of calling the functions doesn't depend on the size of the
   arguments.  We have checked this and there there was no dependence: let's
   leave open the possibility of doing it again in case anything changes.
-}
instance uni ~ DefaultUni => ToBuiltinMeaning uni NopFuns where
    type CostingPart uni NopFuns = NopCostModel
    toBuiltinMeaning
        :: HasConstantIn uni val
           => NopFuns -> BuiltinMeaning val NopCostModel
    toBuiltinMeaning Nop1 =
        makeBuiltinMeaning
             @(Integer -> Integer)
             (\_ -> 11)
             (runCostingFunOneArgument . paramNop1)
    toBuiltinMeaning Nop2 =
        makeBuiltinMeaning
             @(Integer -> Integer -> Integer)
             (\_ _ -> 22)
             (runCostingFunTwoArguments . paramNop2)
    toBuiltinMeaning Nop3 =
        makeBuiltinMeaning
             @(Integer -> Integer -> Integer -> Integer)
             (\_ _ _ -> 33)
             (runCostingFunThreeArguments . paramNop3)
    toBuiltinMeaning Nop4 =
        makeBuiltinMeaning
             @(Integer -> Integer -> Integer -> Integer -> Integer)
             (\_ _ _ _ -> 44)
             (runCostingFunFourArguments . paramNop4)
    toBuiltinMeaning Nop5 =
        makeBuiltinMeaning
             @(Integer -> Integer -> Integer -> Integer -> Integer -> Integer)
             (\_ _ _ _ _ -> 55)
             (runCostingFunFiveArguments . paramNop5)
    toBuiltinMeaning Nop6 =
        makeBuiltinMeaning
             @(Integer -> Integer -> Integer -> Integer -> Integer -> Integer -> Integer)
             (\_ _ _ _ _ _ -> 66)
             (runCostingFunSixArguments . paramNop6)

---------------- Calibration ----------------

{- We want the benchmark results to reflect only the time taken to evaluate a
   builtin, not the startup costs of the CEK machine or the overhead incurred
   while collecting the arguments (applyEvaluate/ forceEvaluate etc).  We
   benchmark the no-op builtins Nop1, Nop2, and Nop3 and in the R code we
   subtract the costs of those from the time recorded for the real builtins.
   Experiments show that the time taken to evaluate these doesn't depend on the
   types or the sizes of the arguments, so we just use functions which consume a
   number of integer arguments and return a constant integer. -}

-- There seems to be quite a lot of variation in repeated runs of these benchmarks.

benchNop1 :: StdGen -> Benchmark
benchNop1 gen =
    let name = Nop1
        mem = 1
        (x,_) = randNwords gen mem
    in bgroup (show name) [benchWith nopCostParameters (showMemoryUsage x) $ mkApp1 name [] x]

benchNop2 :: StdGen -> Benchmark
benchNop2 gen =
    let name = Nop2
        mem = 1
        (x,gen1) = randNwords gen  mem
        (y,_)    = randNwords gen1 mem
    in bgroup (show name)
           [bgroup (showMemoryUsage x)
            [benchWith nopCostParameters (showMemoryUsage y) $ mkApp2 name [] x y]
           ]

benchNop3 :: StdGen -> Benchmark
benchNop3 gen =
    let name = Nop3
        mem = 1
        (x,gen1) = randNwords gen  mem
        (y,gen2) = randNwords gen1 mem
        (z,_)    = randNwords gen2 mem
    in bgroup (show name)
           [bgroup (showMemoryUsage x)
            [bgroup (showMemoryUsage y)
             [benchWith nopCostParameters (showMemoryUsage z) $ mkApp3 name [] x y z]
            ]
           ]

benchNop4 :: StdGen -> Benchmark
benchNop4 gen =
    let name = Nop4
        mem = 1
        (x,gen1) = randNwords gen  mem
        (y,gen2) = randNwords gen1 mem
        (z,gen3) = randNwords gen2 mem
        (t,_)    = randNwords gen3 mem
    in bgroup (show name)
           [bgroup (showMemoryUsage x)
            [bgroup (showMemoryUsage y)
             [bgroup (showMemoryUsage z)
              [benchWith nopCostParameters (showMemoryUsage t) $ mkApp4 name [] x y z t]
             ]
            ]
           ]

benchNop5 :: StdGen -> Benchmark
benchNop5 gen =
    let name = Nop5
        mem = 1
        (x,gen1) = randNwords gen  mem
        (y,gen2) = randNwords gen1 mem
        (z,gen3) = randNwords gen2 mem
        (t,gen4) = randNwords gen3 mem
        (u,_)    = randNwords gen4 mem
    in bgroup (show name)
           [bgroup (showMemoryUsage x)
            [bgroup (showMemoryUsage y)
             [bgroup (showMemoryUsage z)
              [bgroup (showMemoryUsage t)
               [benchWith nopCostParameters (showMemoryUsage u) $ mkApp5 name [] x y z t u]
              ]
             ]
            ]
           ]

benchNop6 :: StdGen -> Benchmark
benchNop6 gen =
    let name = Nop6
        mem = 1
        (x,gen1) = randNwords gen  mem
        (y,gen2) = randNwords gen1 mem
        (z,gen3) = randNwords gen2 mem
        (t,gen4) = randNwords gen3 mem
        (u,gen5) = randNwords gen4 mem
        (v,_)    = randNwords gen5 mem
    in bgroup (show name)
           [bgroup (showMemoryUsage x)
            [bgroup (showMemoryUsage y)
             [bgroup (showMemoryUsage z)
              [bgroup (showMemoryUsage t)
               [bgroup (showMemoryUsage u)
                [benchWith nopCostParameters (showMemoryUsage v) $ mkApp6 name [] x y z t u v]
               ]
              ]
             ]
            ]
           ]

makeBenchmarks :: StdGen -> [Benchmark]
makeBenchmarks gen = [benchNop1 gen, benchNop2 gen, benchNop3 gen, benchNop4 gen, benchNop5 gen, benchNop6 gen]
