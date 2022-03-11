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
import Generators (randBool, randNwords)

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
import System.Random (StdGen)

{- | Arguments to bultins can be treated in several different ways. These benchmarks
   are intended to give some idea of how much overhead each of these involves;  the results
   are used in the R code that we use to fit cost models. -}

data NopFuns
    = Nop1b  -- Bool
    | Nop2b
    | Nop3b
    | Nop4b
    | Nop5b
    | Nop6b
    | Nop1i  -- Integer
    | Nop2i
    | Nop3i
    | Nop4i
    | Nop5i
    | Nop6i
    | Nop1c  -- SomeConstant
    | Nop2c
    | Nop3c
    | Nop4c
    | Nop5c
    | Nop6c
    | Nop1o  -- Opaque: return first argument
    | Nop2o
    | Nop3o
    | Nop4o
    | Nop5o
    | Nop6o
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

{- | The meanings of the builtins.  Each one takes a number of arguments and
   returns a result without doing any other work.  A builtin can process its
   arguments in several different ways (see Note [How to add a built-in
   function]), and these have different costs.  We measure all of these here to
   facilitate cost analysis in the face of future changes in the builtin
   machinery.
-}

instance uni ~ DefaultUni => ToBuiltinMeaning uni NopFuns where
    type CostingPart uni NopFuns = NopCostModel
    toBuiltinMeaning
        :: forall val . HasConstantIn uni val
           => NopFuns -> BuiltinMeaning val NopCostModel
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
    toBuiltinMeaning Nop1c =
        makeBuiltinMeaning
             nop1SomeConstantBool
             (runCostingFunOneArgument . paramNop1)
             where nop1SomeConstantBool :: SomeConstant uni Bool -> EvaluationResult Bool
                   nop1SomeConstantBool b1 =
                       case b1 of
                         SomeConstant (Some (ValueOf DefaultUniBool _)) -> EvaluationSuccess True
                         _                                              -> EvaluationFailure
    toBuiltinMeaning Nop2c =
        makeBuiltinMeaning
             nop2SomeConstantBool
             (runCostingFunTwoArguments . paramNop2)
             where nop2SomeConstantBool :: SomeConstant uni Bool -> SomeConstant uni Bool -> EvaluationResult Bool
                   nop2SomeConstantBool b1 b2 =
                       case b1 of
                         SomeConstant (Some (ValueOf DefaultUniBool _)) ->
                             case b2 of
                               SomeConstant (Some (ValueOf DefaultUniBool _)) -> EvaluationSuccess True
                               _                                              -> EvaluationFailure
                         _ -> EvaluationFailure
    toBuiltinMeaning Nop3c =
        makeBuiltinMeaning
             nop3SomeConstantBool
             (runCostingFunThreeArguments . paramNop3)
             where nop3SomeConstantBool :: SomeConstant uni Bool -> SomeConstant uni Bool
                                        -> SomeConstant uni Bool -> EvaluationResult Bool
                   nop3SomeConstantBool b1 b2 b3 =
                       case b1 of
                         SomeConstant (Some (ValueOf DefaultUniBool _)) ->
                             case b2 of
                               SomeConstant (Some (ValueOf DefaultUniBool _)) ->
                                   case b3 of
                                     SomeConstant (Some (ValueOf DefaultUniBool _)) -> EvaluationSuccess True
                                     _                                              -> EvaluationFailure
                               _ -> EvaluationFailure
                         _ -> EvaluationFailure
    toBuiltinMeaning Nop4c =
        makeBuiltinMeaning
             nop4SomeConstantBool
             (runCostingFunFourArguments . paramNop4)
             where nop4SomeConstantBool :: SomeConstant uni Bool -> SomeConstant uni Bool
                                        -> SomeConstant uni Bool -> SomeConstant uni Bool
                                        -> EvaluationResult Bool
                   nop4SomeConstantBool b1 b2 b3 b4 =
                       case b1 of
                         SomeConstant (Some (ValueOf DefaultUniBool _)) ->
                             case b2 of
                               SomeConstant (Some (ValueOf DefaultUniBool _)) ->
                                   case b3 of
                                     SomeConstant (Some (ValueOf DefaultUniBool _)) ->
                                         case b4 of
                                           SomeConstant (Some (ValueOf DefaultUniBool _)) -> EvaluationSuccess True
                                           _                                              -> EvaluationFailure
                                     _ -> EvaluationFailure
                               _ -> EvaluationFailure
                         _ -> EvaluationFailure
    toBuiltinMeaning Nop5c =
        makeBuiltinMeaning
             nop5SomeConstantBool
             (runCostingFunFiveArguments . paramNop5)
             where nop5SomeConstantBool :: SomeConstant uni Bool -> SomeConstant uni Bool
                                        -> SomeConstant uni Bool -> SomeConstant uni Bool
                                        -> SomeConstant uni Bool -> EvaluationResult Bool
                   nop5SomeConstantBool b1 b2 b3 b4 b5 =
                       case b1 of
                         SomeConstant (Some (ValueOf DefaultUniBool _)) ->
                             case b2 of
                               SomeConstant (Some (ValueOf DefaultUniBool _)) ->
                                   case b3 of
                                     SomeConstant (Some (ValueOf DefaultUniBool _)) ->
                                         case b4 of
                                           SomeConstant (Some (ValueOf DefaultUniBool _)) ->
                                               case b5 of
                                                 SomeConstant (Some (ValueOf DefaultUniBool _)) -> EvaluationSuccess True
                                                 _ -> EvaluationFailure
                                           _ -> EvaluationFailure
                                     _ -> EvaluationFailure
                               _ -> EvaluationFailure
                         _ -> EvaluationFailure

    toBuiltinMeaning Nop6c =
        makeBuiltinMeaning
             nop6SomeConstantBool
             (runCostingFunSixArguments . paramNop6)
             where nop6SomeConstantBool :: SomeConstant uni Bool -> SomeConstant uni Bool
                                        -> SomeConstant uni Bool -> SomeConstant uni Bool
                                        -> SomeConstant uni Bool -> SomeConstant uni Bool
                                        -> EvaluationResult Bool
                   nop6SomeConstantBool b1 b2 b3 b4 b5 b6 =
                       case b1 of
                         SomeConstant (Some (ValueOf DefaultUniBool _)) ->
                             case b2 of
                               SomeConstant (Some (ValueOf DefaultUniBool _)) ->
                                   case b3 of
                                     SomeConstant (Some (ValueOf DefaultUniBool _)) ->
                                         case b4 of
                                           SomeConstant (Some (ValueOf DefaultUniBool _)) ->
                                               case b5 of
                                                 SomeConstant (Some (ValueOf DefaultUniBool _)) ->
                                                     case b6 of
                                                       SomeConstant (Some (ValueOf DefaultUniBool _)) -> EvaluationSuccess True
                                                       _ -> EvaluationFailure
                                                 _ -> EvaluationFailure
                                           _ -> EvaluationFailure
                                     _ -> EvaluationFailure
                               _ -> EvaluationFailure
                         _ -> EvaluationFailure
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

benchNop1b :: StdGen -> Benchmark
benchNop1b gen =
    let name = Nop1b
        (x,_) = randBool gen
    in bgroup (show name) [benchWith nopCostParameters (showMemoryUsage x) $ mkApp1 name [] x]

benchNop2b :: StdGen -> Benchmark
benchNop2b gen =
    let name = Nop2b
        (x,gen1) = randBool gen
        (y,_)    = randBool gen1
    in bgroup (show name)
           [bgroup (showMemoryUsage x)
            [benchWith nopCostParameters (showMemoryUsage y) $ mkApp2 name [] x y]
           ]

benchNop3b :: StdGen -> Benchmark
benchNop3b gen =
    let name = Nop3b
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

benchNop1c :: StdGen -> Benchmark
benchNop1c gen =
    let name = Nop1c
        (x,_) = randBool gen
    in bgroup (show name) [benchWith nopCostParameters (showMemoryUsage x) $ mkApp1 name [] x]

benchNop2c :: StdGen -> Benchmark
benchNop2c gen =
    let name = Nop2c
        (x,gen1) = randBool gen
        (y,_)    = randBool gen1
    in bgroup (show name)
           [bgroup (showMemoryUsage x)
            [benchWith nopCostParameters (showMemoryUsage y) $ mkApp2 name [] x y]
           ]

benchNop3c :: StdGen -> Benchmark
benchNop3c gen =
    let name = Nop3c
        (x,gen1) = randBool gen
        (y,gen2) = randBool gen1
        (z,_)    = randBool gen2
    in bgroup (show name)
           [bgroup (showMemoryUsage x)
            [bgroup (showMemoryUsage y)
             [benchWith nopCostParameters (showMemoryUsage z) $ mkApp3 name [] x y z]
            ]
           ]

benchNop4c :: StdGen -> Benchmark
benchNop4c gen =
    let name = Nop4c
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

benchNop5c :: StdGen -> Benchmark
benchNop5c gen =
    let name = Nop5c
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

benchNop6c :: StdGen -> Benchmark
benchNop6c gen =
    let name = Nop6c
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

makeBenchmarks :: StdGen -> [Benchmark]
makeBenchmarks gen = [ benchNop1i gen, benchNop2i gen, benchNop3i gen, benchNop4i gen, benchNop5i gen, benchNop6i gen
                     , benchNop1b gen, benchNop2b gen, benchNop3b gen, benchNop4b gen, benchNop5b gen, benchNop6b gen
                     , benchNop1c gen, benchNop2c gen, benchNop3c gen, benchNop4c gen, benchNop5c gen, benchNop6c gen
                     , benchNop1o gen, benchNop2o gen, benchNop3o gen, benchNop4o gen, benchNop5o gen, benchNop6o gen ]

