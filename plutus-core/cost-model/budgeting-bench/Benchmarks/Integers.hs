module Benchmarks.Integers (makeBenchmarks) where

import           Benchmarks.Common

import           PlutusCore
import           PlutusCore.Evaluation.Machine.ExMemory

import           Criterion.Main
import           System.Random                          (StdGen)

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

{-# NOINLINE incInteger #-}
incInteger :: Integer -> Integer
incInteger n = n+1

{-# NOINLINE decInteger #-}
decInteger :: Integer -> Integer
decInteger n = n-1

{-# NOINLINE copyInteger #-}
copyInteger :: Integer -> Integer
copyInteger = decInteger . incInteger

-- Given a list [n_1, n_2, ...] create a list [m_1, m_2, ...] where m_i is an n_i-word random integer
makeSizedIntegers :: [Integer] -> StdGen -> ([Integer], StdGen)
makeSizedIntegers [] g = ([], g)
makeSizedIntegers (n:ns) g =
    let (m,g1) = randNwords n g
        (ms,g2) = makeSizedIntegers ns g1
    in (m:ms,g2)

{- For benchmarking functions with integer arguments we provide a list of random
   integers with 1,3,5,...,31 words.  Experiments suggest that these give us good
   models of the behaviour of functions for "reasonable" inputs (which will in
   fact probably only occupy one word).  We still need to guard against denial
   of service, and we may need to impose penalties for *really* large inputs. -}
makeDefaultIntegerArgs :: StdGen -> ([Integer], StdGen)
makeDefaultIntegerArgs gen = makeSizedIntegers [1, 3..31] gen

benchTwoIntegers :: StdGen -> DefaultFun -> Benchmark
benchTwoIntegers gen builtinName =
    createTwoTermBuiltinBench builtinName inputs inputs
    where
      (numbers,_) = makeDefaultIntegerArgs gen
      inputs  = fmap (\e -> (e, memoryUsage e)) numbers


{- Some larger inputs for cases where we're using the same number for both
   arguments.  (A) If we're not examining all NxN pairs then we can eaxmine
   larger arguments without taking too much time. (B) for things like EqInteger
   the results are very uniform with the smaller numbers, leading to occasional
   models with negative slopes.  Using larger numbers may help to avoid this. -}
makeBiggerIntegerArgs :: StdGen -> ([Integer], StdGen)
makeBiggerIntegerArgs gen = makeSizedIntegers [1, 3..101] gen

benchSameTwoIntegers :: StdGen -> DefaultFun -> Benchmark
benchSameTwoIntegers gen builtinName = createTwoTermBuiltinBenchElementwise builtinName inputs inputs'
    where
      (numbers,_) = makeBiggerIntegerArgs gen
      inputs  = fmap (\e -> (e, memoryUsage e)) numbers
      inputs' = fmap (\e -> (e, memoryUsage e)) $ map copyInteger $ numbers




makeBenchmarks :: StdGen -> [Benchmark]
makeBenchmarks gen =
    (benchTwoIntegers gen <$> [ AddInteger, MultiplyInteger, DivideInteger])
    <> (benchSameTwoIntegers gen <$> [ EqualsInteger, LessThanInteger, LessThanEqualsInteger])

