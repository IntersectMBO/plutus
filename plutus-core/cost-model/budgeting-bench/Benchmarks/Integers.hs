module Benchmarks.Integers (makeBenchmarks) where

import Common
import Generators

import PlutusCore
import PlutusCore.Evaluation.Machine.ExMemoryUsage (IntegerCostedByLog (..))


import Criterion.Main
import GHC.Num.Integer
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

{-
benchExpModInteger :: StdGen -> Benchmark
benchExpModInteger _gen =
  let builtinName = ExpModInteger
      pow (a::Integer) (b::Integer) = a^b
      p = (pow 2 255)
      -- 2^255 + 400 = 2^4 × 3 × 9907 × 644977 × 97 674011
      --   × 1932 601194 339139 344835 240473 879578 700967 872768 315843 651779
--      d = p `div` 20
--      inputs = fmap (\n -> 2^n-1) [1,10..255::Integer]
      inputs = fmap (\n -> 2^n-1) [1,20..255::Integer]
      moduli = [p]
  in createThreeTermBuiltinBenchWithWrappers
     (IntegerCostedByLog, IntegerCostedByLog, IntegerCostedByLog)
     builtinName []
     (fmap (\n -> n) inputs)
     (fmap (\n -> n) inputs)
     moduli
-}

{-
benchExpModInteger2 :: StdGen -> Benchmark
benchExpModInteger2 _gen =
  let builtinName = ExpModInteger
      pow (a::Integer) (b::Integer) = a^b
--      p = (pow 2 255) - 19
      p = (pow 2 100) + 400
      -- 2^255 + 400 = 2^4 × 3 × 9907 × 644977 × 97674011
      --   × 1932601194339139344835240473879578700967872768315843651779
--      d = p `div` 20
--      inputs = fmap (\n -> 2^n-1) [1,10..255::Integer]
      xs = fmap (\n -> pow 2 (16*n) - 999) [1..625]  -- up to 2^10000 - 999
      ys = [pow 2 250]
      moduli = [p]
  in createThreeTermBuiltinBenchWithWrappers
     (IntegerCostedByLog, IntegerCostedByLog, IntegerCostedByLog)
     builtinName []
     xs
     ys
     moduli
-- 1669877/248/256
-}

{- The time taken by `expModInteger a b m` doesn't depend too much on a (as long
 as it's not something like 0 or 1), but it does depend on `b` and `m`.  So we
 benchmark with b and m varying over quite a large range, but a fixed for each m.
-}
{- For fixed m and a, the time taken varies linearly with log a (ie, the number of
   bits); for fixed a and b, the time taken varies quadratically with log m.
   Overall we get a good fit with t~I(y*z^2)+I(y*z).
-}

-- Takes about 50 minutes with 625 inputs.
benchExpModInteger :: StdGen -> Benchmark
benchExpModInteger _gen =
  let fun = ExpModInteger
      pow (a::Integer) (b::Integer) = a^b
      moduli = fmap (\n -> pow 2 (32*n) - 11) [1, 3..25]
      -- 256*n for size 800
      bs = fmap (\n -> pow 2 (fromIntegral $ integerLog2 n) - 1) moduli
      -- ^ Largest number less than modulus with binary expansion 1111...1
      -- Should be about worst case

  in bgroup (show fun)
     [bgroup (showMemoryUsage (IntegerCostedByLog (z `div` 3)))
       [bgroup (showMemoryUsage (IntegerCostedByLog y))
         [mkBM x y z | x <- [z `div` 3] ] | y <- bs ] | z <- moduli ]
  where mkBM x y z =
          benchDefault (showMemoryUsage (IntegerCostedByLog z)) $
          mkApp3 ExpModInteger [] x y z


{- Benchmark over a 3-dimensional space of inputs: takes ~6 hours
-}
{-
benchExpModInteger :: StdGen -> Benchmark
benchExpModInteger _gen =
  let fun = ExpModInteger
      pow (a::Integer) (b::Integer) = a^b

      as = (pow 2 255 -19) : fmap (\n -> pow 2 (32*n) - 999) [25,50..625]  -- up to 2^10000 - 999

      moduli = fmap (\n -> pow 2 (256*n) - 11) [1, 3..25]
      bs = [1] -- fmap (\n -> pow 2 (fromIntegral $ integerLog2 n) - 1) moduli
      -- ^ Largest number less than modulus with binary expansion 1111...1
      -- Should be about worst case
--      moduli = fmap (\n -> pow 2 (80*n) - 11) [1, 3..25]
--      Byte sizes = [10,30,50,70,90,110,130,150,170,190,210,230,250] : up to 2^2000
      -- ^ Approximately [2^40, 2^80, ..., 2^1000], but we don't want powers of 2
      -- as = fmap (\n -> n `div` 3) moduli

  in createThreeTermBuiltinBenchWithWrappers
     (IntegerCostedByLog, IntegerCostedByLog, IntegerCostedByLog)
     fun
     []
     as
     bs
     moduli
-}

makeBenchmarks :: StdGen -> [Benchmark]
makeBenchmarks gen =
       [benchTwoIntegers gen makeLargeIntegerArgs AddInteger]-- SubtractInteger behaves identically.
    <> (benchTwoIntegers gen makeDefaultIntegerArgs <$> [MultiplyInteger, DivideInteger])
           -- RemainderInteger, QuotientInteger, and ModInteger all behave identically.
    <> (benchSameTwoIntegers gen <$> [ EqualsInteger
                                     , LessThanInteger
                                     , LessThanEqualsInteger
                                     ])
    <> [-- benchExpModInteger gen,
        benchExpModInteger gen]
