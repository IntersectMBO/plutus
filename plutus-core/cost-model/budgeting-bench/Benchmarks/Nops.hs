{-# LANGUAGE BangPatterns          #-}
{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE InstanceSigs          #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE ViewPatterns          #-}

{- | A set of no-op built-in functions used in cost model calibration. Benchmarks
   based on these are used to estimate the overhead of calling a built-in
   function.
-}

module Benchmarks.Nops (makeBenchmarks, makeBenchmarks') where

import Common
import Generators (randBool, randNwords)

import PlutusCore
import PlutusCore.Builtin
import PlutusCore.Compiler.Erase (eraseTerm)
import PlutusCore.Evaluation.Machine.BuiltinCostModel hiding (BuiltinCostModel)
import PlutusCore.Evaluation.Machine.ExBudgetingDefaults
import PlutusCore.Evaluation.Machine.ExMemoryUsage (ExMemoryUsage)
import PlutusCore.Evaluation.Machine.MachineParameters
import PlutusCore.Evaluation.Result (evaluationFailure)
import PlutusCore.MkPlc (builtin, mkConstant, mkIterAppNoAnn, mkIterInstNoAnn)
import PlutusCore.Pretty
import PlutusPrelude
import UntypedPlutusCore qualified as UPLC
import UntypedPlutusCore.Evaluation.Machine.Cek

import Control.DeepSeq (force)
import Criterion.Main (Benchmark, bgroup)

import Data.Ix (Ix)
import System.Random (StdGen)

-- | Take a function and a list of arguments and apply the former to the latter.
headSpine :: Opaque val asToB -> [val] -> Opaque (HeadSpine val) b
headSpine (Opaque f) = Opaque . \case
    []      -> HeadOnly f
    x0 : xs ->
        -- It's critical to use 'foldr' here, so that deforestation kicks in.
        -- See Note [Definition of foldl'] in "GHC.List" and related Notes around for an explanation
        -- of the trick.
        HeadSpine f $ foldr (\x2 r x1 -> SpineCons x1 $ r x2) SpineLast xs x0
{-# INLINE headSpine #-}

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
    | Nop1r  -- Return a HeadSpine object; inputs are terms to be applied
    | Nop2r
    | Nop3r
    | Nop4r
    | Nop5r
    | Nop6r
    deriving stock (Show, Eq, Ord, Enum, Ix, Bounded, Generic)
    deriving anyclass (NFData, PrettyBy PrettyConfigPlc)

instance Pretty NopFun where
    pretty fun = pretty $ lowerInitialChar $ show fun

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
        CostModel defaultCekMachineCostsForTesting nopCostModel

-- This is just to avoid some deeply nested case expressions for the NopNc
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
      _                                                 -> evaluationFailure
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
instance uni ~ DefaultUni => ToBuiltinMeaning uni NopFun where
    type CostingPart uni NopFun = NopCostModel

    data BuiltinSemanticsVariant NopFun = NopFunSemanticsVariantX

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
             (\c1 -> c1 >: BuiltinSuccess 11)
             (runCostingFunOneArgument . paramNop1)
    toBuiltinMeaning _semvar Nop2c =
        makeBuiltinMeaning
             (\c1 c2 -> c1 >: c2 >: BuiltinSuccess 22)
             (runCostingFunTwoArguments . paramNop2)
    toBuiltinMeaning _semvar Nop3c =
        makeBuiltinMeaning
             (\c1 c2 c3 -> c1 >: c2 >: c3 >: BuiltinSuccess 33)
             (runCostingFunThreeArguments . paramNop3)
    toBuiltinMeaning _semvar Nop4c =
        makeBuiltinMeaning
             (\c1 c2 c3 c4 -> c1 >: c2 >: c3 >: c4 >: BuiltinSuccess 44)
             (runCostingFunFourArguments . paramNop4)
    toBuiltinMeaning _semvar Nop5c =
        makeBuiltinMeaning
             (\c1 c2 c3 c4 c5 -> c1 >: c2 >: c3 >: c4 >: c5 >: BuiltinSuccess 55)
             (runCostingFunFiveArguments . paramNop5)
    toBuiltinMeaning _semvar Nop6c =
        makeBuiltinMeaning
             (\c1 c2 c3 c4 c5 c6 -> c1 >: c2 >: c3 >: c4 >: c5 >: c6 >: BuiltinSuccess 66)
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

-- N functions, 1 argument.  Switch on argument, apply function to K arguments
-- For caseList N=2 and K={0,2}; for caseData, N=5 and K={1,2}.
-- Make our functions of the form \_ _ -> Int (different return values so they're not all the same)

    -- Things returning a HeadSpine.  We have to give them values to be applied
    -- to.  Experiments show that the position of the thing that's being applied
    -- doesn't matter: we take the final one.
    toBuiltinMeaning _semvar Nop1r =
      let nop1rDenotation
            :: Opaque val (() -> Integer -> b)
            -> Opaque (HeadSpine val) b
          nop1rDenotation f1 = headSpine f1 []
          {-# INLINE nop1rDenotation #-}
          in makeBuiltinMeaning
             nop1rDenotation
             (runCostingFunOneArgument . paramNop1)
    toBuiltinMeaning _semvar Nop2r =
      let nop2rDenotation
            :: Opaque val (() -> Integer -> b)
            -> Integer
            -> Opaque (HeadSpine val) b
          nop2rDenotation f1 x = headSpine f1 [fromValue (), fromValue x]
          {-# INLINE nop2rDenotation #-}
          in makeBuiltinMeaning
             nop2rDenotation
             (runCostingFunTwoArguments . paramNop2)
    toBuiltinMeaning _semvar Nop3r =
      let nop3rDenotation
            :: Opaque val (() -> Integer -> b)
            -> Opaque val (() -> Integer -> b)
            -> Integer
            -> Opaque (HeadSpine val) b
          nop3rDenotation _f1 f2 x = headSpine f2 [fromValue (), fromValue x]
          {-# INLINE nop3rDenotation #-}
          in makeBuiltinMeaning
             nop3rDenotation
             (runCostingFunThreeArguments . paramNop3)
    toBuiltinMeaning _semvar Nop4r =
      let nop4rDenotation
            :: Opaque val (() -> Integer -> b)
            -> Opaque val (() -> Integer -> b)
            -> Opaque val (() -> Integer -> b)
            -> Integer
            -> Opaque (HeadSpine val) b
          nop4rDenotation _f1 _f2 f3 x = headSpine f3 [fromValue (), fromValue x]
          {-# INLINE nop4rDenotation #-}
          in makeBuiltinMeaning
             nop4rDenotation
             (runCostingFunFourArguments . paramNop4)
    toBuiltinMeaning _semvar Nop5r =
      let nop5rDenotation
            :: Opaque val (() -> Integer -> b)
            -> Opaque val (() -> Integer -> b)
            -> Opaque val (() -> Integer -> b)
            -> Opaque val (() -> Integer -> b)
            -> Integer
            -> Opaque (HeadSpine val) b
          nop5rDenotation _f1 _f2 _f3 f4 x = headSpine f4 [fromValue (), fromValue x]
          {-# INLINE nop5rDenotation #-}
          in makeBuiltinMeaning
             nop5rDenotation
             (runCostingFunFiveArguments . paramNop5)
    toBuiltinMeaning _semvar Nop6r =
      let nop6rDenotation
            :: Opaque val (() -> Integer -> b)
            -> Opaque val (() -> Integer -> b)
            -> Opaque val (() -> Integer -> b)
            -> Opaque val (() -> Integer -> b)
            -> Opaque val (() -> Integer -> b)
            -> Integer
            -> Opaque (HeadSpine val) b
          nop6rDenotation _f1 _f2 _f3 _f4 f5 x = headSpine f5 [fromValue (), fromValue x]
          {-# INLINE nop6rDenotation #-}
          in makeBuiltinMeaning
             nop6rDenotation
             (runCostingFunSixArguments . paramNop6)

instance Default (BuiltinSemanticsVariant NopFun) where
    def = NopFunSemanticsVariantX

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
benchNop1 nop1 rand gen =
  let (x,_) = rand gen
  in bgroup (show nop1) [benchWith nopCostParameters (showMemoryUsage x) $ mkApp1 nop1 [] x]

benchNop2
  :: (ExMemoryUsage a, DefaultUni `HasTermLevel` a, NFData a)
  => NopFun
  -> (StdGen -> (a, StdGen))
  -> StdGen
  -> Benchmark
benchNop2 nop2 rand gen =
  let (x,gen1) = rand gen
      (y,_)    = rand gen1
  in bgroup (show nop2)
     [bgroup (showMemoryUsage x)
       [benchWith nopCostParameters (showMemoryUsage y) $ mkApp2 nop2 [] x y]
     ]

benchNop3
  :: (ExMemoryUsage a, DefaultUni `HasTermLevel` a, NFData a)
  => NopFun
  -> (StdGen -> (a, StdGen))
  -> StdGen
  -> Benchmark
benchNop3 nop3 rand gen =
  let (x,gen1) = rand gen
      (y,gen2) = rand gen1
      (z,_)    = rand gen2
  in bgroup (show nop3)
     [bgroup (showMemoryUsage x)
       [bgroup (showMemoryUsage y)
         [benchWith nopCostParameters (showMemoryUsage z) $ mkApp3 nop3 [] x y z]
       ]
     ]

benchNop4
  :: (ExMemoryUsage a, DefaultUni `HasTermLevel` a, NFData a)
  => NopFun
  -> (StdGen -> (a, StdGen))
  -> StdGen
  -> Benchmark
benchNop4 nop4 rand gen =
  let (x,gen1) = rand gen
      (y,gen2) = rand gen1
      (z,gen3) = rand gen2
      (t,_)    = rand gen3
  in bgroup (show nop4)
     [bgroup (showMemoryUsage x)
       [bgroup (showMemoryUsage y)
         [bgroup (showMemoryUsage z)
           [benchWith nopCostParameters (showMemoryUsage t) $ mkApp4 nop4 [] x y z t]
         ]
       ]
     ]

benchNop5
  :: (ExMemoryUsage a, DefaultUni `HasTermLevel` a, NFData a)
  => NopFun
  -> (StdGen -> (a, StdGen))
  -> StdGen
  -> Benchmark
benchNop5 nop5 rand gen =
  let (x,gen1) = rand gen
      (y,gen2) = rand gen1
      (z,gen3) = rand gen2
      (t,gen4) = rand gen3
      (u,_)    = rand gen4
  in bgroup (show nop5)
     [bgroup (showMemoryUsage x)
       [bgroup (showMemoryUsage y)
         [bgroup (showMemoryUsage z)
           [bgroup (showMemoryUsage t)
             [benchWith nopCostParameters (showMemoryUsage u) $ mkApp5 nop5 [] x y z t u]
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
benchNop6 nop6 rand gen =
  let (x,gen1) = rand gen
      (y,gen2) = rand gen1
      (z,gen3) = rand gen2
      (t,gen4) = rand gen3
      (u,gen5) = rand gen4
      (v,_)    = rand gen5
  in bgroup (show nop6)
     [bgroup (showMemoryUsage x)
       [bgroup (showMemoryUsage y)
         [bgroup (showMemoryUsage z)
           [bgroup (showMemoryUsage t)
             [bgroup (showMemoryUsage u)
               [benchWith nopCostParameters (showMemoryUsage v) $ mkApp6 nop6 [] x y z t u v]
             ]
           ]
         ]
       ]
     ]


-- For HeadSpine, our generator should return a two-argument function that returns a random integer.
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
    where mkBMs
            :: (DefaultUni `Contains` b, ExMemoryUsage b, NFData b)
            => ((NopFun -> (StdGen -> (b, StdGen)) -> StdGen -> Benchmark) -> t -> a)
            -> (t, t, t, t, t, t)
            -> [a]
          mkBMs mkBM (nop1, nop2, nop3, nop4, nop5, nop6) =
              [ mkBM benchNop1 nop1
              , mkBM benchNop2 nop2
              , mkBM benchNop3 nop3
              , mkBM benchNop4 nop4
              , mkBM benchNop5 nop5
              , mkBM benchNop6 nop6 ]
          mkBmB benchfn nop = benchfn nop randBool gen
          mkBmI benchfn nop = benchfn nop (randNwords 1) gen

instantiate
  :: fun
  -> [Type tyname uni ()]
  -> Term tyname name uni fun ()
instantiate fun tys = mkIterInstNoAnn (builtin () fun) tys


mkApp1'
  :: (UPLC.HasUnique name UPLC.TermUnique, Contains uni a, NFData a)
  => fun
  -> [Type tyname uni ()]
  -> a
  -> UPLC.Term name uni fun ()
mkApp1' !fun !tys (force -> !x) =
  eraseTerm $ mkIterAppNoAnn (instantiate fun tys) [mkConstant () x]

mkApp2'
  :: (UPLC.HasUnique name UPLC.TermUnique, Contains uni a, NFData a)
  => fun
  -> [Type tyname uni ()]
  -> Term tyname name uni fun ()
  -> a
  -> UPLC.Term name uni fun ()
mkApp2' !fun !tys !term1 (force -> !x) =
  eraseTerm $ mkIterAppNoAnn (instantiate fun tys) [term1, mkConstant () x]

mkApp3'
  :: (UPLC.HasUnique name UPLC.TermUnique, Contains uni a, NFData a)
  => fun
  -> [Type tyname uni ()]
  -> Term tyname name uni fun ()
  -> Term tyname name uni fun ()
  -> a
  -> UPLC.Term name uni fun ()
mkApp3' !fun !tys !term1 !term2 (force -> !x) =
  eraseTerm $ mkIterAppNoAnn (instantiate fun tys) [term1, term2, mkConstant () x]

mkApp4'
  :: (UPLC.HasUnique name UPLC.TermUnique, Contains uni a, NFData a)
  => fun
  -> [Type tyname uni ()]
  -> Term tyname name uni fun ()
  -> Term tyname name uni fun ()
  -> Term tyname name uni fun ()
  -> a
  -> UPLC.Term name uni fun ()
mkApp4' !fun !tys !term1 !term2 !term3  (force -> !x) =
  eraseTerm $ mkIterAppNoAnn (instantiate fun tys) [term1, term2, term3, mkConstant () x]

mkApp5'
  :: (UPLC.HasUnique name UPLC.TermUnique, Contains uni a, NFData a)
  => fun
  -> [Type tyname uni ()]
  -> Term tyname name uni fun ()
  -> Term tyname name uni fun ()
  -> Term tyname name uni fun ()
  -> Term tyname name uni fun ()
  -> a
  -> UPLC.Term name uni fun ()
mkApp5' !fun !tys !term1 !term2 !term3 !term4 (force -> !x) =
  eraseTerm $ mkIterAppNoAnn (instantiate fun tys) [term1, term2, term3, term4, mkConstant () x]

mkApp6'
  :: (UPLC.HasUnique name UPLC.TermUnique, Contains uni a, NFData a)
  => fun
  -> [Type tyname uni ()]
  -> Term tyname name uni fun ()
  -> Term tyname name uni fun ()
  -> Term tyname name uni fun ()
  -> Term tyname name uni fun ()
  -> Term tyname name uni fun ()
  -> a
  -> UPLC.Term name uni fun ()
mkApp6' !fun !tys !term1 !term2 !term3 !term4 !term5 (force -> !x) =
  eraseTerm $
  mkIterAppNoAnn (instantiate fun tys)
  [term1, term2, term3, term4, term5, mkConstant () x]

benchNop1'
  :: NopFun
  -> (StdGen -> (Term TyName Name DefaultUni NopFun (), StdGen))
  -> StdGen
  -> Benchmark
benchNop1' nop1 _rand _gen =
  let n = 11 :: Integer
  in bgroup (show nop1) [benchWith nopCostParameters (showMemoryUsage n) $ mkApp1' nop1 [unit] n]

benchNop2'
  :: NopFun
  -> (StdGen -> (Term TyName Name DefaultUni NopFun (), StdGen))
  -> StdGen
  -> Benchmark
benchNop2' nop2 rand gen =
  let (x,_) = rand gen
      n = 22 :: Integer
  in bgroup (show nop2)
     [bgroup "1"
       [benchWith nopCostParameters (showMemoryUsage n) $ mkApp2' nop2 [unit] x n]
     ]

benchNop3'
  :: NopFun
  -> (StdGen -> (Term TyName Name DefaultUni NopFun (), StdGen))
  -> StdGen
  -> Benchmark
benchNop3' nop3 rand gen =
  let (x,gen1) = rand gen
      (y,_)    = rand gen1
      n = 33 :: Integer
  in bgroup (show nop3)
     [bgroup "1"
       [bgroup "1"
         [benchWith nopCostParameters (showMemoryUsage n) $ mkApp3' nop3 [unit] x y n]
       ]
     ]

benchNop4'
  :: NopFun
  -> (StdGen -> (Term TyName Name DefaultUni NopFun (), StdGen))
  -> StdGen
  -> Benchmark
benchNop4' nop4 rand gen =
  let (x,gen1) = rand gen
      (y,gen2) = rand gen1
      (z,_)    = rand gen2
      n = 44 :: Integer
  in bgroup (show nop4)
     [bgroup "1"  -- There is an ExMemoryUsage instance, but "showMemoryUsage" causes an error.
       [bgroup "1" -- We don't care about the size of the term anyway, since it just passed through.
         [bgroup "1"
           [benchWith nopCostParameters (showMemoryUsage n) $ mkApp4' nop4 [unit] x y z n]
         ]
       ]
     ]

-- WAIT! The arguments are actually typed terms at the point where we call
-- showMemoryUsage, but after we create the full term we erase it.  Should we
-- just create untyped terms instead?

benchNop5'
  :: NopFun
  -> (StdGen -> (Term TyName Name DefaultUni NopFun (), StdGen))
  -> StdGen
  -> Benchmark
benchNop5' nop5 rand gen =
  let (x,gen1) = rand gen
      (y,gen2) = rand gen1
      (z,gen3) = rand gen2
      (t,_)    = rand gen3
      n = 55 :: Integer
  in bgroup (show nop5)
     [bgroup "1"
       [bgroup "1"
         [bgroup "1"
           [bgroup "1"
             [benchWith nopCostParameters (showMemoryUsage n) $ mkApp5' nop5 [unit] x y z t n]
           ]
         ]
       ]
     ]


benchNop6'
  :: NopFun
  -> (StdGen -> (Term TyName Name DefaultUni NopFun (), StdGen))
  -> StdGen
  -> Benchmark
benchNop6' nop6 rand gen =
  let (x,gen1) = rand gen
      (y,gen2) = rand gen1
      (z,gen3) = rand gen2
      (t,gen4) = rand gen3
      (u,_)    = rand gen4
      n = 66 :: Integer
  in bgroup (show nop6)
     [bgroup "1"
       [bgroup "1"
         [bgroup "1"
           [bgroup "1"
             [bgroup "1"
               [benchWith nopCostParameters (showMemoryUsage n) $
                mkApp6' nop6 [unit] x y z t u n]
             ]
           ]
         ]
       ]
     ]

makeBenchmarks' :: StdGen -> [Benchmark]
makeBenchmarks' gen0 =
  mkBMs mkBmR (Nop1r, Nop2r, Nop3r, Nop4r, Nop5r, Nop6r)
  where mkBMs mkBM (nop1, nop2, nop3, nop4, nop5, nop6) =
          [ mkBM benchNop1' nop1
          , mkBM benchNop2' nop2
          , mkBM benchNop3' nop3
          , mkBM benchNop4' nop4
          , mkBM benchNop5' nop5
          , mkBM benchNop6' nop6 ]
        mkBmR benchfn nop = benchfn nop randFun gen0
        randFun :: StdGen -> (Term TyName Name DefaultUni NopFun (), StdGen)
        -- \(u:unit) -> \(n:integer) -> x (random integer)
        randFun gen =
          let (_x,gen') = randNwords 1 gen
              u = Name "u" (Unique 1)
              n = Name "n" (Unique 2)
          in (LamAbs () u unit (LamAbs () n integer (mkConstant () ())), gen')


