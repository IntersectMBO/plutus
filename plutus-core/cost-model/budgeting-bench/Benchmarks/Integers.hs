module Benchmarks.Integers (makeBenchmarks) where

import Common
import Generators
import PlutusCore

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
makeDefaultIntegerArgs gen = makeSizedIntegers gen [1, 3 .. 31] -- 16 entries

{- The default arguments give a constant costing function for addition and subtraction.
   These ones give us data where the linear trend is clear. -}
makeLargeIntegerArgs :: StdGen -> ([Integer], StdGen)
makeLargeIntegerArgs gen = makeSizedIntegers gen [1, 70 .. 1000] -- 15 entries

benchTwoIntegers :: StdGen -> (StdGen -> ([Integer], StdGen)) -> DefaultFun -> Benchmark
benchTwoIntegers gen makeArgs builtinName =
  createTwoTermBuiltinBench builtinName [] inputs inputs'
  where
    (inputs, gen') = makeArgs gen
    (inputs', _) = makeArgs gen'

{- Some larger inputs for cases where we're using the same number for both
   arguments.  (A) If we're not examining all NxN pairs then we can examine
   larger arguments without taking too much time. (B) for things like EqInteger
   the results are very uniform with the smaller numbers, leading to occasional
   models with negative slopes.  Using larger numbers may help to avoid this. -}
makeBiggerIntegerArgs :: StdGen -> ([Integer], StdGen)
makeBiggerIntegerArgs gen = makeSizedIntegers gen [1, 3 .. 101]

benchSameTwoIntegers :: StdGen -> DefaultFun -> Benchmark
benchSameTwoIntegers gen builtinName =
  createTwoTermBuiltinBenchElementwise builtinName [] $ pairWith copyInteger numbers
  where
    (numbers, _) = makeBiggerIntegerArgs gen

{- `expModInteger a e m` calculates `a^e` modulo `m`; if `e` is negative then the
function fails unless gcd(a,m) = 1, in which case there is an integer `a'` such
that `a*a'` is congruent to 1 modulo `m`, and then `expModInteger a e m` is
defined to be `expModInteger a' (-e) m`.  If `0 <= a <= m-1` and `e>=0` then the
time taken by expModInteger varies linearly with the size of `e` (and the worst
case is when `e` is one less than a power of two) and quadratically with the
size of `m`.  A good model can be obtained by fitting a function of the form A +
Byz + Cyz^2 (y=size(e), z=size(m)) to the results of the benchmarks.  For most
values of `a` (except for things like 0 and 1), the time taken for
exponentiation is independent of the size of `a` because many intermediate
powers have to be calculated, and these quickly grow so that their size is
similar to that of `m`.  In the benchmarks we use `a = m div 3` to start with a
value of reasonable size.

For exponents `e<0` a little extra time is required to perform an initial
modular inversion, but this only adds a percent or two to the execution time so
for simplicity we benchmark only with positive values of `e`. For values of `a`
with `size(a)>size(m)` an extra modular reduction has to be performed before
starting the main calculation.  It is difficult to model the effect of this
precisely, so we impose an extra charge by increasing the cost of
`expModInteger` by 50% for values of `a` with large sizes; to avoid the penalty,
call `modInteger` before calling `expModInteger`.
-}
benchExpModInteger :: StdGen -> Benchmark
benchExpModInteger _gen =
  let fun = ExpModInteger
      pow (a :: Integer) (b :: Integer) = a ^ b
      moduli = fmap (\n -> pow 2 (32 * n) - 11) [1, 3 .. 31]
      -- \^ 16 entries, sizes = 4, 12, ..., 124 bytes (memoryUsage = 1,2,...,16)
      es = fmap (\n -> pow 2 (fromIntegral $ integerLog2 n) - 1) moduli
   in -- \^ Largest number less than modulus with binary expansion 1111...1.
      -- This is the worst case.

      bgroup
        (show fun)
        [ bgroup
            (showMemoryUsage (m `div` 3))
            [ bgroup
                (showMemoryUsage e)
                [mkBM a e m | a <- [m `div` 3]]
            | e <- es
            ]
        | m <- moduli
        ]
  where
    mkBM a e m =
      benchDefault (showMemoryUsage m) $
        mkApp3 ExpModInteger [] a e m

makeBenchmarks :: StdGen -> [Benchmark]
makeBenchmarks gen =
  [benchTwoIntegers gen makeLargeIntegerArgs AddInteger] -- SubtractInteger behaves identically.
    <> (benchTwoIntegers gen makeDefaultIntegerArgs <$> [MultiplyInteger, DivideInteger])
    -- RemainderInteger, QuotientInteger, and ModInteger all behave identically.
    <> ( benchSameTwoIntegers gen
           <$> [ EqualsInteger
               , LessThanInteger
               , LessThanEqualsInteger
               ]
       )
    <> [ -- benchExpModInteger gen,
         benchExpModInteger gen
       ]
