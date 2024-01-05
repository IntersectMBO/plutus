{-# OPTIONS_GHC -fno-warn-unused-top-binds #-}
{-# OPTIONS_GHC -fno-warn-unused-imports #-}

module Benchmarks.Bitwise (makeBenchmarks) where

import Common
import Generators

import PlutusCore

import Criterion.Main
import Data.ByteString qualified as BS
import System.Random (StdGen, randomR)

import Hedgehog qualified as H

---------------- ByteString builtins ----------------

integerLength :: BS.ByteString -> Integer
integerLength = fromIntegral . BS.length

-- Arguments for single-argument benchmarks: 150 entries.
-- Note that the length is eight times the size.
smallerByteStrings150 :: H.Seed -> [BS.ByteString]
smallerByteStrings150 seed = makeSizedByteStrings seed $ fmap (10*) [1..150]

-- Arguments for two-argument benchmarks: 21 entries.
-- Note that the length is eight times the size.
largerByteStrings21 :: H.Seed -> [BS.ByteString]
largerByteStrings21 seed = makeSizedByteStrings seed $ fmap (250*) [0..20]

smallerIntegers150 :: StdGen -> [Integer]
smallerIntegers150 gen = fst $ makeSizedIntegers gen $ fmap (10*) [1..150]

benchTwoByteStrings :: DefaultFun -> Benchmark
benchTwoByteStrings name =
    createTwoTermBuiltinBench name [] (largerByteStrings21 seedA) (largerByteStrings21 seedB)

benchByteStringToIntegerTrue :: Benchmark
benchByteStringToIntegerTrue =
    bgroup name $ fmap mkBM (smallerByteStrings150 seedA)
        where mkBM b = benchDefault (showMemoryUsage b) $ mkApp2 ByteStringToInteger [] True b
              name = "ByteStringToIntegerTrue"

benchByteStringToIntegerFalse :: Benchmark
benchByteStringToIntegerFalse =
    bgroup name $ fmap mkBM (smallerByteStrings150 seedA)
        where mkBM b = benchDefault (showMemoryUsage b) $ mkApp2 ByteStringToInteger [] False b
              name = "ByteStringToIntegerFalse"


benchIntegerToByteStringTrue0 :: StdGen -> Benchmark
benchIntegerToByteStringTrue0 gen =
    bgroup name $ fmap mkBM (smallerIntegers150 gen)
        where mkBM b = benchDefault (showMemoryUsage b) $
                       mkApp3 IntegerToByteString [] True (0::Integer) b
              name = "IntegerToByteStringTrue0"

benchIntegerToByteStringFalse0 :: StdGen -> Benchmark
benchIntegerToByteStringFalse0 gen =
    bgroup name $ fmap mkBM (smallerIntegers150 gen)
        where mkBM b = benchDefault (showMemoryUsage b) $
                       mkApp3 IntegerToByteString [] False (0::Integer) b
              name = "IntegerToByteStringFalse0"

mkBmW :: String -> Bool -> [Integer] -> [Integer] -> Benchmark
mkBmW name flag xs ys =
    bgroup name $ zipWith (\x y -> bgroup (show x) [mkBM x y]) xs ys
        where mkBM x y = benchDefault (showMemoryUsage y) $ mkApp3 IntegerToByteString [] flag x y

mkBmW2 :: String -> Bool -> Benchmark
mkBmW2 name flag =
    let widths = fmap (80*) [1..150]
        inputs = fmap (\n -> 256^n - 1) widths
    in mkBmW name flag widths inputs

benchIntegerToByteStringWTrue :: Benchmark
benchIntegerToByteStringWTrue =
    mkBmW2 "IntegerToByteStringWTrue" True

benchIntegerToByteStringWFalse :: Benchmark
benchIntegerToByteStringWFalse =
    mkBmW2 "IntegerToByteStringWFalse" False

makeBenchmarks :: StdGen -> [Benchmark]
makeBenchmarks gen =
    [ benchByteStringToIntegerFalse,
      benchByteStringToIntegerTrue,
      benchIntegerToByteStringFalse0 gen,
      benchIntegerToByteStringTrue0 gen,
      benchIntegerToByteStringWFalse,
      benchIntegerToByteStringWTrue
    ]
{-    <> [benchDifferentByteStringsElementwise EqualsByteString]
      <> (benchSameTwoByteStrings <$>
                        [ EqualsByteString, LessThanEqualsByteString, LessThanByteString ])
-}

{- Results for bytestrings of size integerPower 2 <$> [1..20::Integer].  The
   biggest inputs here are of size 1048576, or about 4 megabytes.  That's surely
   too big.  Maybe try [1000, 2000, ..., 100000] oor [100, 200, ..., 10000] for
   one-argument functions and [500, 1000, ..., 10000] for two-argument
   functions.


   AppendByteString : good fit for I(x+y), but underpredicts for reasonably-sized
   inputs

   EqualsByteString LessThanEqualsByteString, LessThanByteString: these all
   agree to within 2%, but the plot bends up towards the right.  You get a
   pretty good linear fit for sizes less than 250000

   ConsByteString: this does appear to be linear in the size of the string, and
   the size of the thing you're consing is irrelevant.  Again, the inputs are a
   bit too big.

   LengthOfByteString: this does appear to be pretty much constant, although
   it's hard to tell over the exponential range of scales we have here.  The
   time taken varies between 888ns and 1143ns, but randomly.  We could do with
   more data points here, and more uniformly spaced.

   IndexByteString: again this looks constant.  More uniform spacing would be
   good.

   SliceByteString: again, pretty constant.

   Overall it looks like we'd get good models with smaller and evenly spaced
   strings. We should do this but check what happens with larger inputs for
   AppendByteString.  We should also give more inputs to the single-argument
   functions.

-}
