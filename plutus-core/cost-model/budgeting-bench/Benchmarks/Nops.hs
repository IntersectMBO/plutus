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

{- | A benchmark that just loads the unit constant, which is about the minimal
   amount of work we can do.  This should give an idea of the cost of starting
   the evaluator. -}
benchUnitTerm :: Benchmark
benchUnitTerm =
    bgroup "UnitTerm" [benchWith nopCostParameters (showMemoryUsage ()) $ mkUnit ]


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

data NNopFun
    = NNop1b  -- Built-in Bool
    | NNop2b
    | NNop3b
    | NNop4b
    | NNop5b
    | NNop6b
    | NNop1i  -- Built-in Integer
    | NNop2i
    | NNop3i
    | NNop4i
    | NNop5i
    | NNop6i
    | NNop1c  -- Integer: lifted via SomeConstant
    | NNop2c
    | NNop3c
    | NNop4c
    | NNop5c
    | NNop6c
    | NNop1o  -- Opaque Integer: no unlifting required
    | NNop2o
    | NNop3o
    | NNop4o
    | NNop5o
    | NNop6o
    deriving stock (Show, Eq, Ord, Enum, Ix, Bounded, Generic)
    deriving anyclass (PrettyBy PrettyConfigPlc)

instance Pretty NNopFun where
    pretty fun = pretty $ lowerInitialChar $ show fun

data NNopCostModel =
    NNopCostModel
    { paramNNop1 :: CostingFun ModelOneArgument
    , paramNNop2 :: CostingFun ModelTwoArguments
    , paramNNop3 :: CostingFun ModelThreeArguments
    , paramNNop4 :: CostingFun ModelFourArguments
    , paramNNop5 :: CostingFun ModelFiveArguments
    , paramNNop6 :: CostingFun ModelSixArguments
    }

{- | A fake cost model for nops.  This is just to make sure that the overhead of
   calling a costing function of the expected form is included, so the precise
   contents don't matter as long as the basic form is correct (and benchmarks
   suggest that nops indeed have constant costs). -}
nopCostModel :: NNopCostModel
nopCostModel =
    NNopCostModel
    {
      paramNNop1 = CostingFun
                  (ModelOneArgumentConstantCost 1000000)
                  (ModelOneArgumentConstantCost 100)
    , paramNNop2 = CostingFun
                  (ModelTwoArgumentsConstantCost 1250000)
                  (ModelTwoArgumentsConstantCost 200)
    , paramNNop3 = CostingFun
                  (ModelThreeArgumentsConstantCost 1500000)
                  (ModelThreeArgumentsConstantCost 300)
    , paramNNop4 = CostingFun
                  (ModelFourArgumentsConstantCost 1750000)
                  (ModelFourArgumentsConstantCost 400)
    , paramNNop5 = CostingFun
                  (ModelFiveArgumentsConstantCost 2000000)
                  (ModelFiveArgumentsConstantCost 500)
    , paramNNop6 = CostingFun
                  (ModelSixArgumentsConstantCost 2250000)
                  (ModelSixArgumentsConstantCost 600)
    }

nopCostParameters :: MachineParameters CekMachineCosts NNopFun (CekValue DefaultUni NNopFun ())
nopCostParameters =
    MachineParameters def . mkMachineVariantParameters def $
        CostModel defaultCekMachineCostsForTesting nopCostModel

-- This is just to avoid some deeply nested case expressions for the NNopNc
-- functions below.  There is a Monad instance for EvaluationResult, but that
-- appears to be a little slower than this.
infixr >:
(>:) :: uni ~ DefaultUni
     => SomeConstant uni Integer
     -> BuiltinResult Integer
     -> BuiltinResult Integer
n >: k =
    case n of
      SomeConstant (Some (ValueOf DefaultUniInteger _)) -> k
      _                                                 -> builtinResultFailure
{-# INLINE (>:) #-}

{- | The meanings of the builtins.  Each one takes a number of arguments and
   returns a result without doing any other work.  A builtin can process its
   arguments in several different ways (see Note [How to add a built-in
   function: simple cases] etc.), and these have different costs.  We measure
   all of these here to facilitate exploration of their different contributions
   to execution costs (which may change if there are changes in the builtin
   machinery in future).  Most of the builtins take Integers since we can easily
   change the sizes of these to check that the size doesn't influence the cost;
   we also have some nops over Bool to check that the type doesn't influence the
   cost either.
-}
instance uni ~ DefaultUni => ToBuiltinMeaning uni NNopFun where
    type CostingPart uni NNopFun = NNopCostModel

    data BuiltinSemanticsVariant NNopFun = NNopFunSemanticsVariantX

    -- Built-in Bools
    toBuiltinMeaning
        :: forall val . HasMeaningIn uni val
        => BuiltinSemanticsVariant NNopFun
        -> NNopFun
        -> BuiltinMeaning val NNopCostModel
    toBuiltinMeaning _semvar NNop1b =
        makeBuiltinMeaning
             @(Bool -> Bool)
             (\_ -> True)
             (runCostingFunOneArgument . paramNNop1)
    toBuiltinMeaning _semvar NNop2b =
        makeBuiltinMeaning
             @(Bool -> Bool -> Bool)
             (\_ _ -> True)
             (runCostingFunTwoArguments . paramNNop2)
    toBuiltinMeaning _semvar NNop3b =
        makeBuiltinMeaning
             @(Bool -> Bool -> Bool -> Bool)
             (\_ _ _ -> True)
             (runCostingFunThreeArguments . paramNNop3)
    toBuiltinMeaning _semvar NNop4b =
        makeBuiltinMeaning
             @(Bool -> Bool -> Bool -> Bool -> Bool)
             (\_ _ _ _ -> True)
             (runCostingFunFourArguments . paramNNop4)
    toBuiltinMeaning _semvar NNop5b =
        makeBuiltinMeaning
             @(Bool -> Bool -> Bool -> Bool -> Bool -> Bool)
             (\_ _ _ _ _ -> True)
             (runCostingFunFiveArguments . paramNNop5)
    toBuiltinMeaning _semvar NNop6b =
        makeBuiltinMeaning
             @(Bool -> Bool -> Bool -> Bool -> Bool -> Bool -> Bool)
             (\_ _ _ _ _ _ -> True)
             (runCostingFunSixArguments . paramNNop6)
    -- Built-in Integers
    toBuiltinMeaning _semvar NNop1i =
        makeBuiltinMeaning
             @(Integer -> Integer)
             (\_ -> 11)
             (runCostingFunOneArgument . paramNNop1)
    toBuiltinMeaning _semvar NNop2i =
        makeBuiltinMeaning
             @(Integer -> Integer -> Integer)
             (\_ _ -> 22)
             (runCostingFunTwoArguments . paramNNop2)
    toBuiltinMeaning _semvar NNop3i =
        makeBuiltinMeaning
             @(Integer -> Integer -> Integer -> Integer)
             (\_ _ _ -> 33)
             (runCostingFunThreeArguments . paramNNop3)
    toBuiltinMeaning _semvar NNop4i =
        makeBuiltinMeaning
             @(Integer -> Integer -> Integer -> Integer -> Integer)
             (\_ _ _ _ -> 44)
             (runCostingFunFourArguments . paramNNop4)
    toBuiltinMeaning _semvar NNop5i =
        makeBuiltinMeaning
             @(Integer -> Integer -> Integer -> Integer -> Integer -> Integer)
             (\_ _ _ _ _ -> 55)
             (runCostingFunFiveArguments . paramNNop5)
    toBuiltinMeaning _semvar NNop6i =
        makeBuiltinMeaning
             @(Integer -> Integer -> Integer -> Integer -> Integer -> Integer -> Integer)
             (\_ _ _ _ _ _ -> 66)
             (runCostingFunSixArguments . paramNNop6)
    -- Integers unlifted via SomeConstant
    toBuiltinMeaning _semvar NNop1c =
        makeBuiltinMeaning
             (\c1 -> c1 >: BuiltinSuccess 11)
             (runCostingFunOneArgument . paramNNop1)
    toBuiltinMeaning _semvar NNop2c =
        makeBuiltinMeaning
             (\c1 c2 -> c1 >: c2 >: BuiltinSuccess 22)
             (runCostingFunTwoArguments . paramNNop2)
    toBuiltinMeaning _semvar NNop3c =
        makeBuiltinMeaning
             (\c1 c2 c3 -> c1 >: c2 >: c3 >: BuiltinSuccess 33)
             (runCostingFunThreeArguments . paramNNop3)
    toBuiltinMeaning _semvar NNop4c =
        makeBuiltinMeaning
             (\c1 c2 c3 c4 -> c1 >: c2 >: c3 >: c4 >: BuiltinSuccess 44)
             (runCostingFunFourArguments . paramNNop4)
    toBuiltinMeaning _semvar NNop5c =
        makeBuiltinMeaning
             (\c1 c2 c3 c4 c5 -> c1 >: c2 >: c3 >: c4 >: c5 >: BuiltinSuccess 55)
             (runCostingFunFiveArguments . paramNNop5)
    toBuiltinMeaning _semvar NNop6c =
        makeBuiltinMeaning
             (\c1 c2 c3 c4 c5 c6 -> c1 >: c2 >: c3 >: c4 >: c5 >: c6 >: BuiltinSuccess 66)
             (runCostingFunSixArguments . paramNNop6)
    -- Opaque Integers
    toBuiltinMeaning _semvar NNop1o =
        makeBuiltinMeaning
             @(Opaque val Integer -> Opaque val Integer)
             (\_ -> fromValueOf DefaultUniInteger 11)
             (runCostingFunOneArgument . paramNNop1)
    toBuiltinMeaning _semvar NNop2o =
        makeBuiltinMeaning
             @(Opaque val Integer -> Opaque val Integer-> Opaque val Integer)
             (\_ _ -> fromValueOf DefaultUniInteger 22)
             (runCostingFunTwoArguments . paramNNop2)
    toBuiltinMeaning _semvar NNop3o =
        makeBuiltinMeaning
             @(Opaque val Integer -> Opaque val Integer-> Opaque val Integer-> Opaque val Integer)
             (\_ _ _ -> fromValueOf DefaultUniInteger 33)
             (runCostingFunThreeArguments . paramNNop3)
    toBuiltinMeaning _semvar NNop4o =
        makeBuiltinMeaning
             @(Opaque val Integer
                -> Opaque val Integer
                -> Opaque val Integer
                -> Opaque val Integer
                -> Opaque val Integer)
             (\_ _ _ _ -> fromValueOf DefaultUniInteger 44)
             (runCostingFunFourArguments . paramNNop4)
    toBuiltinMeaning _semvar NNop5o =
        makeBuiltinMeaning
             @(Opaque val Integer -> Opaque val Integer-> Opaque val Integer
               -> Opaque val Integer -> Opaque val Integer -> Opaque val Integer)
             (\_ _ _ _ _ -> fromValueOf DefaultUniInteger 55)
             (runCostingFunFiveArguments . paramNNop5)
    toBuiltinMeaning _semvar NNop6o =
        makeBuiltinMeaning
             @(Opaque val Integer -> Opaque val Integer-> Opaque val Integer
               -> Opaque val Integer -> Opaque val Integer -> Opaque val Integer
               -> Opaque val Integer)
             (\_ _ _ _ _ _ -> fromValueOf DefaultUniInteger 66)
             (runCostingFunSixArguments . paramNNop6)

instance Default (BuiltinSemanticsVariant NNopFun) where
    def = NNopFunSemanticsVariantX

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

{- | `benchNNopN` generates N random inputs and makes a benchmark measuring how
   long it takes the given function to run with those arguments.  Take care that
   N matches the number of arguments of the function or else you'll be
   benchmarking an overapplication (which will fail) or a partial application
   (which will succeed, but would give misleading results).  For example, only
   apply benchNNop5 to a NNop5 function, not to something like NNop6i or NNop2o.
 -}

benchNNop1
    :: (ExMemoryUsage a, DefaultUni `HasTermLevel` a, NFData a)
    => NNopFun
    -> (StdGen -> (a, StdGen))
    -> StdGen
    -> Benchmark
benchNNop1 nop rand gen =
    let (x,_) = rand gen
    in bgroup (show nop) [benchWith nopCostParameters (showMemoryUsage x) $ mkApp1 nop [] x]

benchNNop2
    :: (ExMemoryUsage a, DefaultUni `HasTermLevel` a, NFData a)
    => NNopFun
    -> (StdGen -> (a, StdGen))
    -> StdGen
    -> Benchmark
benchNNop2 nop rand gen =
    let (x,gen1) = rand gen
        (y,_)    = rand gen1
    in bgroup (show nop)
           [bgroup (showMemoryUsage x)
            [benchWith nopCostParameters (showMemoryUsage y) $ mkApp2 nop [] x y]
           ]

benchNNop3
    :: (ExMemoryUsage a, DefaultUni `HasTermLevel` a, NFData a)
    => NNopFun
    -> (StdGen -> (a, StdGen))
    -> StdGen
    -> Benchmark
benchNNop3 nop rand gen =
    let (x,gen1) = rand gen
        (y,gen2) = rand gen1
        (z,_)    = rand gen2
    in bgroup (show nop)
           [bgroup (showMemoryUsage x)
            [bgroup (showMemoryUsage y)
             [benchWith nopCostParameters (showMemoryUsage z) $ mkApp3 nop [] x y z]
            ]
           ]

benchNNop4
    :: (ExMemoryUsage a, DefaultUni `HasTermLevel` a, NFData a)
    => NNopFun
    -> (StdGen -> (a, StdGen))
    -> StdGen
    -> Benchmark
benchNNop4 nop rand gen =
    let (x,gen1) = rand gen
        (y,gen2) = rand gen1
        (z,gen3) = rand gen2
        (t,_)    = rand gen3
    in bgroup (show nop)
           [bgroup (showMemoryUsage x)
            [bgroup (showMemoryUsage y)
             [bgroup (showMemoryUsage z)
              [benchWith nopCostParameters (showMemoryUsage t) $ mkApp4 nop [] x y z t]
             ]
            ]
           ]

benchNNop5
    :: (ExMemoryUsage a, DefaultUni `HasTermLevel` a, NFData a)
    => NNopFun
    -> (StdGen -> (a, StdGen))
    -> StdGen
    -> Benchmark
benchNNop5 nop rand gen =
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
               [benchWith nopCostParameters (showMemoryUsage u) $ mkApp5 nop [] x y z t u]
              ]
             ]
            ]
           ]

benchNNop6
    :: (ExMemoryUsage a, DefaultUni `HasTermLevel` a, NFData a)
    => NNopFun
    -> (StdGen -> (a, StdGen))
    -> StdGen
    -> Benchmark
benchNNop6 nop rand gen =
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
                [benchWith nopCostParameters (showMemoryUsage v) $ mkApp6 nop [] x y z t u v]
               ]
              ]
             ]
            ]
           ]


-- | The actual benchmarks
makeBenchmarks :: StdGen -> [Benchmark]
makeBenchmarks gen =
    [ benchUnitTerm ]
    ++ mkBMs mkBmB (NNop1b, NNop2b, NNop3b, NNop4b, NNop5b, NNop6b)
    ++ mkBMs mkBmI (NNop1i, NNop2i, NNop3i, NNop4i, NNop5i, NNop6i)
    ++ mkBMs mkBmI (NNop1c, NNop2c, NNop3c, NNop4c, NNop5c, NNop6c)
    ++ mkBMs mkBmI (NNop1o, NNop2o, NNop3o, NNop4o, NNop5o, NNop6o)
   -- The subsidiary functions below make it a lot easier to see that we're
   -- benchmarking the right things with the right benchmarking functions.
   -- Maybe we could use some TH instead.
    where mkBMs mkBM (nop1, nop2, nop3, nop4, nop5, nop6) =
              [ mkBM benchNNop1 nop1
              , mkBM benchNNop2 nop2
              , mkBM benchNNop3 nop3
              , mkBM benchNNop4 nop4
              , mkBM benchNNop5 nop5
              , mkBM benchNNop6 nop6 ]
          mkBmB benchfn nop = benchfn nop randBool gen
          mkBmI benchfn nop = benchfn nop (randNwords 1)  gen
          -- Benchmark using Integer inputs with memory usage 1
