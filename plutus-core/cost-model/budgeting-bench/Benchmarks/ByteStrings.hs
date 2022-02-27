module Benchmarks.ByteStrings (makeBenchmarks) where

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

benchTwoByteStrings :: DefaultFun -> Benchmark
benchTwoByteStrings name = createTwoTermBuiltinBench name [] (largerByteStrings21 seedA) (largerByteStrings21 seedB)

benchLengthOfByteString :: Benchmark
benchLengthOfByteString =
    bgroup (show name) $ fmap mkBM (smallerByteStrings150 seedA)
        where mkBM b = benchDefault (showMemoryUsage b) $ mkApp1 name [] b
              name = LengthOfByteString

-- Copy the byteString here, because otherwise it'll be exactly the same and the equality will short-circuit.
benchSameTwoByteStrings :: DefaultFun -> Benchmark
benchSameTwoByteStrings name = createTwoTermBuiltinBenchElementwise name [] inputs (fmap BS.copy inputs)
    where inputs = smallerByteStrings150 seedA

-- Here we benchmark different pairs of bytestrings elementwise.  This is used
-- to get times for off-diagonal comparisons, which we expect to be roughly
-- constant since the equality test returns quickly in that case.
benchDifferentByteStringsElementwise :: DefaultFun -> Benchmark
benchDifferentByteStringsElementwise name = createTwoTermBuiltinBenchElementwise name [] inputs1 inputs2
    where inputs1 = smallerByteStrings150 seedA
          inputs2 = smallerByteStrings150 seedB

-- This is constant, even for large inputs
benchIndexByteString :: StdGen -> Benchmark
benchIndexByteString gen = createTwoTermBuiltinBenchElementwise IndexByteString [] bytestrings (randomIndices gen bytestrings)
    where bytestrings = smallerByteStrings150 seedA
          randomIndices gen1 l =
              case l of
                [] -> []
                b:bs -> let (i,gen2) = randomR (0, (integerLength b)-1) gen1
                        in i:randomIndices gen2 bs

{- This should be constant time, since the underlying operations are just
   returning modified pointers into a C array.  We still want a decent number of
   data points, so we generate ten bytestrings of size 100, 200, ..., 1000 and
   for each of them look at four choices each of starting index and length of
   slice (so 16 (index,length) pairs for each bytestring size). -}
benchSliceByteString :: Benchmark
benchSliceByteString =
    let name = SliceByteString
        quarters n = if n < 4 then [n] else [0, t..(n-t)] where t = n `div` 4
        -- quarters n may contain more than four elements if n < 16, but we
        -- won't encounter that case.  For n<4 then the 'else' branch would give
        -- you an infinite list of zeros.
        byteStrings = makeSizedByteString seedA <$> fmap (100*) [1..10]
        mkBMsFor b =
            [bgroup (showMemoryUsage start)
             [bgroup (showMemoryUsage len)
              [benchDefault (showMemoryUsage b) $ mkApp3 name [] start len b] |
              len <- quarters (blen - start)] |
             start <- quarters blen]
            where blen = integerLength b
    in bgroup (show name) $ concatMap mkBMsFor byteStrings


benchConsByteString :: Benchmark
benchConsByteString =
    createTwoTermBuiltinBench ConsByteString [] [n] (smallerByteStrings150 seedA)
        where n = 123456789 :: Integer
        -- The precise numbers don't seem to matter here.  There'll be
        -- some cost coercing them to Word8, but even with very large
        -- numbers that seems to be negligible.


makeBenchmarks :: StdGen -> [Benchmark]
makeBenchmarks gen =  [ benchTwoByteStrings AppendByteString,
                        benchConsByteString,
                        benchLengthOfByteString,
                        benchIndexByteString gen,
                        benchSliceByteString
                      ]
                      <> [benchDifferentByteStringsElementwise EqualsByteString]
                      <> (benchSameTwoByteStrings <$> [ EqualsByteString, LessThanEqualsByteString, LessThanByteString ])


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
