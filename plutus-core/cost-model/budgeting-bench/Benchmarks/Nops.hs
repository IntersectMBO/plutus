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

import Criterion.Main
import Data.Char (toLower)
import Data.Ix (Ix)
import GHC.Generics (Generic)
import System.Random (StdGen, randomR)

data NopFuns
    = Nop1i  -- Integer
    | Nop2i
    | Nop3i
    | Nop4i
    | Nop5i
    | Nop6i
    | Nop1b  -- Bool
    | Nop2b
    | Nop3b
    | Nop4b
    | Nop5b
    | Nop6b
    | Nop1o  -- Opaque: return first argument
    | Nop2o
    | Nop3o
    | Nop4o
    | Nop5o
    | Nop6o
    | Nop1z  -- Opaque: return final argument
    | Nop2z
    | Nop3z
    | Nop4z
    | Nop5z
    | Nop6z
    deriving stock (Show, Eq, Ord, Enum, Ix, Bounded, Generic)
    deriving anyclass (PrettyBy PrettyConfigPlc)

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
        :: forall val . HasConstantIn uni val
           => NopFuns -> BuiltinMeaning val NopCostModel
    toBuiltinMeaning Nop1i =
        makeBuiltinMeaning
             @(Integer -> Integer)
             (\_ -> 11)
             (runCostingFunOneArgument . paramNop1)
    toBuiltinMeaning Nop2i =
        makeBuiltinMeaning
             @(Integer -> Integer -> Integer)
             (\_ _ -> 22)
             (runCostingFunTwoArguments . paramNop2)
    toBuiltinMeaning Nop3i =
        makeBuiltinMeaning
             @(Integer -> Integer -> Integer -> Integer)
             (\_ _ _ -> 33)
             (runCostingFunThreeArguments . paramNop3)
    toBuiltinMeaning Nop4i =
        makeBuiltinMeaning
             @(Integer -> Integer -> Integer -> Integer -> Integer)
             (\_ _ _ _ -> 44)
             (runCostingFunFourArguments . paramNop4)
    toBuiltinMeaning Nop5i =
        makeBuiltinMeaning
             @(Integer -> Integer -> Integer -> Integer -> Integer -> Integer)
             (\_ _ _ _ _ -> 55)
             (runCostingFunFiveArguments . paramNop5)
    toBuiltinMeaning Nop6i =
        makeBuiltinMeaning
             @(Integer -> Integer -> Integer -> Integer -> Integer -> Integer -> Integer)
             (\_ _ _ _ _ _ -> 66)
             (runCostingFunSixArguments . paramNop6)
    toBuiltinMeaning Nop1b =
        makeBuiltinMeaning
             @(Bool -> Bool)
             (\_ -> True)
             (runCostingFunOneArgument . paramNop1)
    toBuiltinMeaning Nop2b =
        makeBuiltinMeaning
             @(Bool -> Bool -> Bool)
             (\_ _ -> True)
             (runCostingFunTwoArguments . paramNop2)
    toBuiltinMeaning Nop3b =
        makeBuiltinMeaning
             @(Bool -> Bool -> Bool -> Bool)
             (\_ _ _ -> True)
             (runCostingFunThreeArguments . paramNop3)
    toBuiltinMeaning Nop4b =
        makeBuiltinMeaning
             @(Bool -> Bool -> Bool -> Bool -> Bool)
             (\_ _ _ _ -> True)
             (runCostingFunFourArguments . paramNop4)
    toBuiltinMeaning Nop5b =
        makeBuiltinMeaning
             @(Bool -> Bool -> Bool -> Bool -> Bool -> Bool)
             (\_ _ _ _ _ -> True)
             (runCostingFunFiveArguments . paramNop5)
    toBuiltinMeaning Nop6b =
        makeBuiltinMeaning
             @(Bool -> Bool -> Bool -> Bool -> Bool -> Bool -> Bool)
             (\_ _ _ _ _ _ -> True)
             (runCostingFunSixArguments . paramNop6)
    toBuiltinMeaning Nop1o =
        makeBuiltinMeaning
             @(Opaque val Integer -> Opaque val Integer)
             (\x -> x)
             (runCostingFunOneArgument . paramNop1)
    toBuiltinMeaning Nop2o =
        makeBuiltinMeaning
             @(Opaque val Integer -> Opaque val Integer-> Opaque val Integer)
             (\x _ -> x)
             (runCostingFunTwoArguments . paramNop2)
    toBuiltinMeaning Nop3o =
        makeBuiltinMeaning
             @(Opaque val Integer -> Opaque val Integer-> Opaque val Integer-> Opaque val Integer)
             (\x _ _ -> x)
             (runCostingFunThreeArguments . paramNop3)
    toBuiltinMeaning Nop4o =
        makeBuiltinMeaning
             @(Opaque val Integer -> Opaque val Integer-> Opaque val Integer-> Opaque val Integer -> Opaque val Integer)
             (\x _ _ _ -> x)
             (runCostingFunFourArguments . paramNop4)
    toBuiltinMeaning Nop5o =
        makeBuiltinMeaning
             @(Opaque val Integer -> Opaque val Integer-> Opaque val Integer
               -> Opaque val Integer -> Opaque val Integer -> Opaque val Integer)
             (\x _ _ _ _ -> x)
             (runCostingFunFiveArguments . paramNop5)
    toBuiltinMeaning Nop6o =
        makeBuiltinMeaning
             @(Opaque val Integer -> Opaque val Integer-> Opaque val Integer
               -> Opaque val Integer -> Opaque val Integer -> Opaque val Integer -> Opaque val Integer)
             (\x _ _ _ _ _ -> x)
             (runCostingFunSixArguments . paramNop6)
    toBuiltinMeaning Nop1z =
        makeBuiltinMeaning
             @(Opaque val Integer -> Opaque val Integer)
             (\z -> z)
             (runCostingFunOneArgument . paramNop1)
    toBuiltinMeaning Nop2z =
        makeBuiltinMeaning
             @(Opaque val Integer -> Opaque val Integer-> Opaque val Integer)
             (\_ z -> z)
             (runCostingFunTwoArguments . paramNop2)
    toBuiltinMeaning Nop3z =
        makeBuiltinMeaning
             @(Opaque val Integer -> Opaque val Integer-> Opaque val Integer -> Opaque val Integer)
             (\_ _ z -> z)
             (runCostingFunThreeArguments . paramNop3)
    toBuiltinMeaning Nop4z =
        makeBuiltinMeaning
             @(Opaque val Integer -> Opaque val Integer-> Opaque val Integer
               -> Opaque val Integer -> Opaque val Integer)
             (\_ _ _ z -> z)
             (runCostingFunFourArguments . paramNop4)
    toBuiltinMeaning Nop5z =
        makeBuiltinMeaning
             @(Opaque val Integer -> Opaque val Integer-> Opaque val Integer
               -> Opaque val Integer -> Opaque val Integer -> Opaque val Integer)
             (\_ _ _ _ z -> z)
             (runCostingFunFiveArguments . paramNop5)
    toBuiltinMeaning Nop6z =
        makeBuiltinMeaning
             @(Opaque val Integer -> Opaque val Integer-> Opaque val Integer
               -> Opaque val Integer -> Opaque val Integer -> Opaque val Integer -> Opaque val Integer)
             (\_ _ _ _ _ z -> z)
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

benchNop1i :: StdGen -> Benchmark
benchNop1i gen =
    let name = Nop1i
        mem = 1
        (x,_) = randNwords gen mem
    in bgroup (show name) [benchWith nopCostParameters (showMemoryUsage x) $ mkApp1 name [] x]

benchNop2i :: StdGen -> Benchmark
benchNop2i gen =
    let name = Nop2i
        mem = 1
        (x,gen1) = randNwords gen  mem
        (y,_)    = randNwords gen1 mem
    in bgroup (show name)
           [bgroup (showMemoryUsage x)
            [benchWith nopCostParameters (showMemoryUsage y) $ mkApp2 name [] x y]
           ]

benchNop3i :: StdGen -> Benchmark
benchNop3i gen =
    let name = Nop3i
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

benchNop4i :: StdGen -> Benchmark
benchNop4i gen =
    let name = Nop4i
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

benchNop5i :: StdGen -> Benchmark
benchNop5i gen =
    let name = Nop5i
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

benchNop6i :: StdGen -> Benchmark
benchNop6i gen =
    let name = Nop6i
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

randBool :: StdGen -> (Bool, StdGen)
randBool gen = randomR (False, True) gen

benchNop1b :: StdGen -> Benchmark
benchNop1b gen =
    let name = Nop1b
        (x,_) = randBool gen
    in bgroup (show name) [benchWith nopCostParameters (showMemoryUsage x) $ mkApp1 name [] x]

benchNop2b :: StdGen -> Benchmark
benchNop2b gen =
    let name = Nop2b
        mem = 1
        (x,gen1) = randBool gen
        (y,_)    = randBool gen1
    in bgroup (show name)
           [bgroup (showMemoryUsage x)
            [benchWith nopCostParameters (showMemoryUsage y) $ mkApp2 name [] x y]
           ]

benchNop3b :: StdGen -> Benchmark
benchNop3b gen =
    let name = Nop3b
        mem = 1
        (x,gen1) = randBool gen
        (y,gen2) = randBool gen1
        (z,_)    = randBool gen2
    in bgroup (show name)
           [bgroup (showMemoryUsage x)
            [bgroup (showMemoryUsage y)
             [benchWith nopCostParameters (showMemoryUsage z) $ mkApp3 name [] x y z]
            ]
           ]

benchNop4b :: StdGen -> Benchmark
benchNop4b gen =
    let name = Nop4b
        mem = 1
        (x,gen1) = randBool gen
        (y,gen2) = randBool gen1
        (z,gen3) = randBool gen2
        (t,_)    = randBool gen3
    in bgroup (show name)
           [bgroup (showMemoryUsage x)
            [bgroup (showMemoryUsage y)
             [bgroup (showMemoryUsage z)
              [benchWith nopCostParameters (showMemoryUsage t) $ mkApp4 name [] x y z t]
             ]
            ]
           ]

benchNop5b :: StdGen -> Benchmark
benchNop5b gen =
    let name = Nop5b
        mem = 1
        (x,gen1) = randBool gen
        (y,gen2) = randBool gen1
        (z,gen3) = randBool gen2
        (t,gen4) = randBool gen3
        (u,_)    = randBool gen4
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

benchNop6b :: StdGen -> Benchmark
benchNop6b gen =
    let name = Nop6b
        mem = 1
        (x,gen1) = randBool gen
        (y,gen2) = randBool gen1
        (z,gen3) = randBool gen2
        (t,gen4) = randBool gen3
        (u,gen5) = randBool gen4
        (v,_)    = randBool gen5
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

benchNop1o :: StdGen -> Benchmark
benchNop1o gen =
    let name = Nop1o
        mem = 1
        (x,_) = randNwords gen mem
    in bgroup (show name) [benchWith nopCostParameters (showMemoryUsage x) $ mkApp1 name [] x]

benchNop2o :: StdGen -> Benchmark
benchNop2o gen =
    let name = Nop2o
        mem = 1
        (x,gen1) = randNwords gen  mem
        (y,_)    = randNwords gen1 mem
    in bgroup (show name)
           [bgroup (showMemoryUsage x)
            [benchWith nopCostParameters (showMemoryUsage y) $ mkApp2 name [] x y]
           ]

benchNop3o :: StdGen -> Benchmark
benchNop3o gen =
    let name = Nop3o
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

benchNop4o :: StdGen -> Benchmark
benchNop4o gen =
    let name = Nop4o
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

benchNop5o :: StdGen -> Benchmark
benchNop5o gen =
    let name = Nop5o
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

benchNop6o :: StdGen -> Benchmark
benchNop6o gen =
    let name = Nop6o
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

benchNop1z :: StdGen -> Benchmark
benchNop1z gen =
    let name = Nop1z
        (x,_) = randBool gen
    in bgroup (show name) [benchWith nopCostParameters (showMemoryUsage x) $ mkApp1 name [] x]

benchNop2z :: StdGen -> Benchmark
benchNop2z gen =
    let name = Nop2z
        (x,gen1) = randBool gen
        (y,_)    = randBool gen1
    in bgroup (show name)
           [bgroup (showMemoryUsage x)
            [benchWith nopCostParameters (showMemoryUsage y) $ mkApp2 name [] x y]
           ]

benchNop3z :: StdGen -> Benchmark
benchNop3z gen =
    let name = Nop3z
        (x,gen1) = randBool gen
        (y,gen2) = randBool gen1
        (z,_)    = randBool gen2
    in bgroup (show name)
           [bgroup (showMemoryUsage x)
            [bgroup (showMemoryUsage y)
             [benchWith nopCostParameters (showMemoryUsage z) $ mkApp3 name [] x y z]
            ]
           ]

benchNop4z :: StdGen -> Benchmark
benchNop4z gen =
    let name = Nop4z
        (x,gen1) = randBool gen
        (y,gen2) = randBool gen1
        (z,gen3) = randBool gen2
        (t,_)    = randBool gen3
    in bgroup (show name)
           [bgroup (showMemoryUsage x)
            [bgroup (showMemoryUsage y)
             [bgroup (showMemoryUsage z)
              [benchWith nopCostParameters (showMemoryUsage t) $ mkApp4 name [] x y z t]
             ]
            ]
           ]

benchNop5z :: StdGen -> Benchmark
benchNop5z gen =
    let name = Nop5z
        (x,gen1) = randBool gen
        (y,gen2) = randBool gen1
        (z,gen3) = randBool gen2
        (t,gen4) = randBool gen3
        (u,_)    = randBool gen4
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

benchNop6z :: StdGen -> Benchmark
benchNop6z gen =
    let name = Nop6z
        (x,gen1) = randBool gen
        (y,gen2) = randBool gen1
        (z,gen3) = randBool gen2
        (t,gen4) = randBool gen3
        (u,gen5) = randBool gen4
        (v,_)    = randBool gen5
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
makeBenchmarks gen = [ benchNop1i gen, benchNop2i gen, benchNop3i gen, benchNop4i gen, benchNop5i gen, benchNop6i gen
                     , benchNop1b gen, benchNop2b gen, benchNop3b gen, benchNop4b gen, benchNop5b gen, benchNop6b gen
                     , benchNop1o gen, benchNop2o gen, benchNop3o gen, benchNop4o gen, benchNop5o gen, benchNop6o gen
                     , benchNop1z gen, benchNop2z gen, benchNop3z gen, benchNop4z gen, benchNop5z gen, benchNop6z gen]
