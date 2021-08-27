module Benchmarks.Integers (makeBenchmarks) where

import           Benchmarks.Common

import           PlutusCore

import           Criterion.Main
import           System.Random     (StdGen)

---------------- Integer builtins ----------------

{- | In some cases (for example, equality testing) the worst-case behaviour of a
builtin will be when it has two identical arguments However, there's a danger
that if the arguments are physically identical (ie, they are (pointers to) the
same object in the heap) the underlying implementation may notice that and
return immediately.  The code below attempts to avoid this by producing a
complerely new copy of an integer.  Experiments with 'realyUnsafePtrEquality#`
indicate that it does what's required (in fact, `cloneInteger n = (n+1)-1` with
NOINLINE suffices, but that's perhaps a bit too fragile).
-}

{- For benchmarking functions with integer arguments we provide a list of random
   integers with 1,3,5,...,31 words.  Experiments suggest that these give us good
   models of the behaviour of functions for "reasonable" inputs (which will in
   fact probably only occupy one word).  We still need to guard against denial
   of service, and we may need to impose penalties for *really* large inputs. -}
makeDefaultIntegerArgs :: StdGen -> ([Integer], StdGen)
makeDefaultIntegerArgs gen = makeSizedIntegers gen [1, 3..31]

benchTwoIntegers :: StdGen -> DefaultFun -> Benchmark
benchTwoIntegers gen builtinName =
    createTwoTermBuiltinBench builtinName [] inputs inputs
    where
      (inputs,_) = makeDefaultIntegerArgs gen


{- Some larger inputs for cases where we're using the same number for both
   arguments.  (A) If we're not examining all NxN pairs then we can eaxmine
   larger arguments without taking too much time. (B) for things like EqInteger
   the results are very uniform with the smaller numbers, leading to occasional
   models with negative slopes.  Using larger numbers may help to avoid this. -}
makeBiggerIntegerArgs :: StdGen -> ([Integer], StdGen)
makeBiggerIntegerArgs gen = makeSizedIntegers gen [1, 3..101]

benchSameTwoIntegers :: StdGen -> DefaultFun -> Benchmark
benchSameTwoIntegers gen builtinName = createTwoTermBuiltinBenchElementwise builtinName [] inputs inputs'
    where
      (numbers,_) = makeBiggerIntegerArgs gen
      inputs  = numbers
      inputs' = map copyInteger numbers

makeBenchmarks :: StdGen -> [Benchmark]
makeBenchmarks gen =
    (benchTwoIntegers gen <$>
                          [ AddInteger
                          , MultiplyInteger
                          , DivideInteger])
    <> (benchSameTwoIntegers gen <$>
                                 [ EqualsInteger
                                 , LessThanInteger
                                 , LessThanEqualsInteger])

