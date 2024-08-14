module Benchmarks.Integers (makeBenchmarks) where

import Common
import Generators

import PlutusCore

import Criterion.Main
import System.Random (StdGen)

---------------- Integer builtins ----------------

{- For benchmarking functions with integer arguments we provide a list of random
   integers with 1,3,5,...,31 words.  Experiments suggest that these give us good
   models of the behaviour of functions for "reasonable" inputs (which will in
   fact probably only occupy one word).  We still need to guard against denial
   of service, and we may need to impose penalties for *really* large inputs. -}
makeDefaultIntegerArgs :: StdGen -> ([Integer], StdGen)
makeDefaultIntegerArgs gen = makeSizedIntegers gen [1, 3..31] -- 16 entries

{- The default arguments give a constant costing function for addition and subtraction.
   These ones give us data where the linear trend is clear. -}
makeLargeIntegerArgs :: StdGen -> ([Integer], StdGen)
makeLargeIntegerArgs gen = makeSizedIntegers gen [1, 70..1000] -- 15 entries

benchTwoIntegers :: StdGen -> (StdGen -> ([Integer], StdGen)) -> DefaultFun -> Benchmark
benchTwoIntegers gen makeArgs builtinName =
    createTwoTermBuiltinBench builtinName [] inputs inputs'
    where
      (inputs, gen') = makeArgs gen
      (inputs', _)   = makeArgs gen'

{- Some larger inputs for cases where we're using the same number for both
   arguments.  (A) If we're not examining all NxN pairs then we can examine
   larger arguments without taking too much time. (B) for things like EqInteger
   the results are very uniform with the smaller numbers, leading to occasional
   models with negative slopes.  Using larger numbers may help to avoid this. -}
makeBiggerIntegerArgs :: StdGen -> ([Integer], StdGen)
makeBiggerIntegerArgs gen = makeSizedIntegers gen [1, 3..101]

benchSameTwoIntegers :: StdGen -> DefaultFun -> Benchmark
benchSameTwoIntegers gen builtinName =
   createTwoTermBuiltinBenchElementwise builtinName [] $ pairWith copyInteger numbers
    where (numbers,_) = makeBiggerIntegerArgs gen

makeBenchmarks :: StdGen -> [Benchmark]
makeBenchmarks gen =
       [benchTwoIntegers gen makeLargeIntegerArgs AddInteger]-- SubtractInteger behaves identically.
    <> (benchTwoIntegers gen makeDefaultIntegerArgs <$> [MultiplyInteger, DivideInteger])
           -- RemainderInteger, QuotientInteger, and ModInteger all behave identically.
    <> (benchSameTwoIntegers gen <$> [ EqualsInteger
                                     , LessThanInteger
                                     , LessThanEqualsInteger
                                     ])
