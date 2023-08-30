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

import Data.Char (toLower)
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

data NopFun
    = Nop1b  -- Built-in Bool
    | Nop2b
    | Nop3b
    | Nop4b
    | Nop5b
    | Nop6b
    | Nop1i  -- Built-in Integer
    | Nop2i
    | Nop3i
    | Nop4i
    | Nop5i
    | Nop6i
    | Nop1c  -- Integer: lifted via SomeConstant
    | Nop2c
    | Nop3c
    | Nop4c
    | Nop5c
    | Nop6c
    | Nop1o  -- Opaque Integer: no unlifting required
    | Nop2o
    | Nop3o
    | Nop4o
    | Nop5o
    | Nop6o
    deriving stock (Show, Eq, Ord, Enum, Ix, Bounded, Generic)
    deriving anyclass (PrettyBy PrettyConfigPlc)

instance Pretty NopFun where
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
   calling a costing function of the expected form is included, so the precise
   contents don't matter as long as the basic form is correct (and benchmarks
   suggest that nops indeed have constant costs). -}
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

nopCostParameters :: MachineParameters CekMachineCosts NopFun (CekValue DefaultUni NopFun ())
nopCostParameters =
    mkMachineParameters def $
        CostModel defaultCekMachineCosts nopCostModel

-- This is just to avoid some deeply nested case expressions for the NopNc
-- functions below.  There is a Monad instance for EvaluationResult, but that
-- appears to be a little slower than this.
{-# INLINE (>:) #-}
infixr >:
(>:) :: uni ~ DefaultUni
     => SomeConstant uni Integer
     -> EvaluationResult Integer
     -> EvaluationResult Integer
n >: k =
    case n of
      SomeConstant (Some (ValueOf DefaultUniInteger _)) -> k
      _                                                 -> EvaluationFailure

{- | The meanings of the builtins.  Each one takes a number of arguments and
   returns a result without doing any other work.  A builtin can process its
   arguments in several different ways (see Note [How to add a built-in
   function]), and these have different costs.  We measure all of these here to
   facilitate exploration of their different contributions to execution costs
   (which may change if there are changes in the builtin machinery in future).
   Most of the builtins take Integers since we can easily change the sizes of
   these to check that the size doesn't influence the cost; we also have some
   nops over Bool to check that the type doesn't influence the cost either.
-}
instance uni ~ DefaultUni => ToBuiltinMeaning uni NopFun where
    type CostingPart uni NopFun = NopCostModel

    data BuiltinSemanticsVariant NopFun = NopFunSemanticsVariant1

    -- Built-in Bools
    toBuiltinMeaning
        :: forall val . HasMeaningIn uni val
        => BuiltinSemanticsVariant NopFun
        -> NopFun
        -> BuiltinMeaning val NopCostModel
    toBuiltinMeaning _semvar Nop1b =
        makeBuiltinMeaning
             @(Bool -> Bool)
             (\_ -> True)
             (runCostingFunOneArgument . paramNop1)
    toBuiltinMeaning _semvar Nop2b =
        makeBuiltinMeaning
             @(Bool -> Bool -> Bool)
             (\_ _ -> True)
             (runCostingFunTwoArguments . paramNop2)
    toBuiltinMeaning _semvar Nop3b =
        makeBuiltinMeaning
             @(Bool -> Bool -> Bool -> Bool)
             (\_ _ _ -> True)
             (runCostingFunThreeArguments . paramNop3)
    toBuiltinMeaning _semvar Nop4b =
        makeBuiltinMeaning
             @(Bool -> Bool -> Bool -> Bool -> Bool)
             (\_ _ _ _ -> True)
             (runCostingFunFourArguments . paramNop4)
    toBuiltinMeaning _semvar Nop5b =
        makeBuiltinMeaning
             @(Bool -> Bool -> Bool -> Bool -> Bool -> Bool)
             (\_ _ _ _ _ -> True)
             (runCostingFunFiveArguments . paramNop5)
    toBuiltinMeaning _semvar Nop6b =
        makeBuiltinMeaning
             @(Bool -> Bool -> Bool -> Bool -> Bool -> Bool -> Bool)
             (\_ _ _ _ _ _ -> True)
             (runCostingFunSixArguments . paramNop6)
    -- Built-in Integers
    toBuiltinMeaning _semvar Nop1i =
        makeBuiltinMeaning
             @(Integer -> Integer)
             (\_ -> 11)
             (runCostingFunOneArgument . paramNop1)
    toBuiltinMeaning _semvar Nop2i =
        makeBuiltinMeaning
             @(Integer -> Integer -> Integer)
             (\_ _ -> 22)
             (runCostingFunTwoArguments . paramNop2)
    toBuiltinMeaning _semvar Nop3i =
        makeBuiltinMeaning
             @(Integer -> Integer -> Integer -> Integer)
             (\_ _ _ -> 33)
             (runCostingFunThreeArguments . paramNop3)
    toBuiltinMeaning _semvar Nop4i =
        makeBuiltinMeaning
             @(Integer -> Integer -> Integer -> Integer -> Integer)
             (\_ _ _ _ -> 44)
             (runCostingFunFourArguments . paramNop4)
    toBuiltinMeaning _semvar Nop5i =
        makeBuiltinMeaning
             @(Integer -> Integer -> Integer -> Integer -> Integer -> Integer)
             (\_ _ _ _ _ -> 55)
             (runCostingFunFiveArguments . paramNop5)
    toBuiltinMeaning _semvar Nop6i =
        makeBuiltinMeaning
             @(Integer -> Integer -> Integer -> Integer -> Integer -> Integer -> Integer)
             (\_ _ _ _ _ _ -> 66)
             (runCostingFunSixArguments . paramNop6)
    -- Integers unlifted via SomeConstant
    toBuiltinMeaning _semvar Nop1c =
        makeBuiltinMeaning
             (\c1 -> c1 >: EvaluationSuccess 11)
             (runCostingFunOneArgument . paramNop1)
    toBuiltinMeaning _semvar Nop2c =
        makeBuiltinMeaning
             (\c1 c2 -> c1 >: c2 >: EvaluationSuccess 22)
             (runCostingFunTwoArguments . paramNop2)
    toBuiltinMeaning _semvar Nop3c =
        makeBuiltinMeaning
             (\c1 c2 c3 -> c1 >: c2 >: c3 >: EvaluationSuccess 33)
             (runCostingFunThreeArguments . paramNop3)
    toBuiltinMeaning _semvar Nop4c =
        makeBuiltinMeaning
             (\c1 c2 c3 c4 -> c1 >: c2 >: c3 >: c4 >: EvaluationSuccess 44)
             (runCostingFunFourArguments . paramNop4)
    toBuiltinMeaning _semvar Nop5c =
        makeBuiltinMeaning
             (\c1 c2 c3 c4 c5 -> c1 >: c2 >: c3 >: c4 >: c5 >: EvaluationSuccess 55)
             (runCostingFunFiveArguments . paramNop5)
    toBuiltinMeaning _semvar Nop6c =
        makeBuiltinMeaning
             (\c1 c2 c3 c4 c5 c6 -> c1 >: c2 >: c3 >: c4 >: c5 >: c6 >: EvaluationSuccess 66)
             (runCostingFunSixArguments . paramNop6)
    -- Opaque Integers
    toBuiltinMeaning _semvar Nop1o =
        makeBuiltinMeaning
             @(Opaque val Integer -> Opaque val Integer)
             (\_ -> fromValueOf DefaultUniInteger 11)
             (runCostingFunOneArgument . paramNop1)
    toBuiltinMeaning _semvar Nop2o =
        makeBuiltinMeaning
             @(Opaque val Integer -> Opaque val Integer-> Opaque val Integer)
             (\_ _ -> fromValueOf DefaultUniInteger 22)
             (runCostingFunTwoArguments . paramNop2)
    toBuiltinMeaning _semvar Nop3o =
        makeBuiltinMeaning
             @(Opaque val Integer -> Opaque val Integer-> Opaque val Integer-> Opaque val Integer)
             (\_ _ _ -> fromValueOf DefaultUniInteger 33)
             (runCostingFunThreeArguments . paramNop3)
    toBuiltinMeaning _semvar Nop4o =
        makeBuiltinMeaning
             @(Opaque val Integer
                -> Opaque val Integer
                -> Opaque val Integer
                -> Opaque val Integer
                -> Opaque val Integer)
             (\_ _ _ _ -> fromValueOf DefaultUniInteger 44)
             (runCostingFunFourArguments . paramNop4)
    toBuiltinMeaning _semvar Nop5o =
        makeBuiltinMeaning
             @(Opaque val Integer -> Opaque val Integer-> Opaque val Integer
               -> Opaque val Integer -> Opaque val Integer -> Opaque val Integer)
             (\_ _ _ _ _ -> fromValueOf DefaultUniInteger 55)
             (runCostingFunFiveArguments . paramNop5)
    toBuiltinMeaning _semvar Nop6o =
        makeBuiltinMeaning
             @(Opaque val Integer -> Opaque val Integer-> Opaque val Integer
               -> Opaque val Integer -> Opaque val Integer -> Opaque val Integer
               -> Opaque val Integer)
             (\_ _ _ _ _ _ -> fromValueOf DefaultUniInteger 66)
             (runCostingFunSixArguments . paramNop6)

instance Default (BuiltinSemanticsVariant NopFun) where
    def = NopFunSemanticsVariant1

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
    => NopFun
    -> (StdGen -> (a, StdGen))
    -> StdGen
    -> Benchmark
benchNop1 nop rand gen =
    let (x,_) = rand gen
    in bgroup (show nop) [benchWith nopCostParameters (showMemoryUsage x) $ mkApp1 nop [] x]

benchNop2
    :: (ExMemoryUsage a, DefaultUni `HasTermLevel` a, NFData a)
    => NopFun
    -> (StdGen -> (a, StdGen))
    -> StdGen
    -> Benchmark
benchNop2 nop rand gen =
    let (x,gen1) = rand gen
        (y,_)    = rand gen1
    in bgroup (show nop)
           [bgroup (showMemoryUsage x)
            [benchWith nopCostParameters (showMemoryUsage y) $ mkApp2 nop [] x y]
           ]

benchNop3
    :: (ExMemoryUsage a, DefaultUni `HasTermLevel` a, NFData a)
    => NopFun
    -> (StdGen -> (a, StdGen))
    -> StdGen
    -> Benchmark
benchNop3 nop rand gen =
    let (x,gen1) = rand gen
        (y,gen2) = rand gen1
        (z,_)    = rand gen2
    in bgroup (show nop)
           [bgroup (showMemoryUsage x)
            [bgroup (showMemoryUsage y)
             [benchWith nopCostParameters (showMemoryUsage z) $ mkApp3 nop [] x y z]
            ]
           ]

benchNop4
    :: (ExMemoryUsage a, DefaultUni `HasTermLevel` a, NFData a)
    => NopFun
    -> (StdGen -> (a, StdGen))
    -> StdGen
    -> Benchmark
benchNop4 nop rand gen =
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

benchNop5
    :: (ExMemoryUsage a, DefaultUni `HasTermLevel` a, NFData a)
    => NopFun
    -> (StdGen -> (a, StdGen))
    -> StdGen
    -> Benchmark
benchNop5 nop rand gen =
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

benchNop6
    :: (ExMemoryUsage a, DefaultUni `HasTermLevel` a, NFData a)
    => NopFun
    -> (StdGen -> (a, StdGen))
    -> StdGen
    -> Benchmark
benchNop6 nop rand gen =
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
    ++ mkBMs mkBmB (Nop1b, Nop2b, Nop3b, Nop4b, Nop5b, Nop6b)
    ++ mkBMs mkBmI (Nop1i, Nop2i, Nop3i, Nop4i, Nop5i, Nop6i)
    ++ mkBMs mkBmI (Nop1c, Nop2c, Nop3c, Nop4c, Nop5c, Nop6c)
    ++ mkBMs mkBmI (Nop1o, Nop2o, Nop3o, Nop4o, Nop5o, Nop6o)
   -- The subsidiary functions below make it a lot easier to see that we're
   -- benchmarking the right things with the right benchmarking functions.
   -- Maybe we could use some TH instead.
    where mkBMs mkBM (nop1, nop2, nop3, nop4, nop5, nop6) =
              [ mkBM benchNop1 nop1
              , mkBM benchNop2 nop2
              , mkBM benchNop3 nop3
              , mkBM benchNop4 nop4
              , mkBM benchNop5 nop5
              , mkBM benchNop6 nop6 ]
          mkBmB benchfn nop = benchfn nop randBool gen
          mkBmI benchfn nop = benchfn nop (randNwords 1)  gen
          -- Benchmark using Integer inputs with memory usage 1
