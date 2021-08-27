module Benchmarks.ByteStrings (makeBenchmarks) where

import           Benchmarks.Common

import           PlutusCore

import           Criterion.Main
import qualified Data.ByteString   as BS
import           System.Random     (StdGen, randomR)

import qualified Hedgehog          as H

---------------- ByteString builtins ----------------

integerLength :: BS.ByteString -> Integer
integerLength = fromIntegral . BS.length


-- Sizes of the arguments that we're goint to use as inputs to the bytestring builtin benchmarks.
-- These are sizes in words, so the actual bytestrings will be 8 times longer, ie [0, 2000..40000]
byteStringSizes :: [Integer]
byteStringSizes = [0, 250..5000]  -- 21 entries.
-- byteStringSizes = integerPower 2 <$> [1..20::Integer]

byteStringsToBench :: H.Seed -> [BS.ByteString]
byteStringsToBench seed = (makeSizedByteString seed . fromInteger) <$> byteStringSizes

benchTwoByteStrings :: DefaultFun -> Benchmark
benchTwoByteStrings name = createTwoTermBuiltinBench name (byteStringsToBench seedA) (byteStringsToBench seedB)

benchByteStringNoArgOperations :: DefaultFun -> Benchmark
benchByteStringNoArgOperations name =
    bgroup (show name) $ fmap mkBM (byteStringsToBench seedA)
        where mkBM b = benchDefault (showMemoryUsage b) $ mkApp1 name [] b

-- Copy the byteString here, because otherwise it'll be exactly the same, and the equality will short-circuit.
benchSameTwoByteStrings :: DefaultFun -> Benchmark
benchSameTwoByteStrings name = createTwoTermBuiltinBenchElementwise name (byteStringsToBench seedA)
                               (fmap BS.copy $ byteStringsToBench seedA)

benchIndexByteString :: StdGen -> Benchmark
benchIndexByteString gen = createTwoTermBuiltinBenchElementwise IndexByteString bytestrings (randomIndices gen bytestrings)
    where bytestrings = byteStringsToBench seedA
          randomIndices gen1 l =
              case l of
                [] -> []
                b:bs -> let (i,gen2) = randomR (0, (integerLength b)-1) gen1
                        in i:randomIndices gen2 bs

{- This should be constant time, since the underlying operations are just
   returning modified pointers into a C array.  We still want a decent number of
   data points, so we generate bytestrings of length 1000, 2000, ..., 10000 and
   for each of them look at four choices each of index and length. -}
benchSliceByteString :: Benchmark
benchSliceByteString =
    let name = SliceByteString
        quarters n = if n < 4 then [n] else [0, t..(n-t)] where t = n `div` 4
        -- quarters n may contain more than four elements if n < 16, but we
        -- won't encounter that case.  For n<4 then the 'else' branch would give
        -- you an infinite list of zeros.
        byteStrings = makeSizedByteString seedA <$> [1000, 2000..10000]
        mkBMsFor b =
            [bgroup (showMemoryUsage start)
             [bgroup (showMemoryUsage len)
              [benchDefault (showMemoryUsage b) $ mkApp3 name [] start len b] |
              len <- quarters (blen - start)] |
             start <- quarters blen]
            where blen = integerLength b
    in bgroup (show name) $ concatMap mkBMsFor byteStrings

benchConsByteString :: Benchmark
benchConsByteString = createTwoTermBuiltinBench ConsByteString numbers (byteStringsToBench seedA)
                      where numbers = fmap (1000 *) [100, 200..2000] :: [Integer]
             -- In fact the numbers don't seem to matter here.  There'll be some
             -- cost coercing them to Word8, but even with very large numbers
             -- that seems to be negligible.
             -- FIXME: This takes a long time, so confirm that the size of the first argument
             -- is irrelevant and pass a list of 100 or so bytestrings.

makeBenchmarks :: StdGen -> [Benchmark]
makeBenchmarks gen =  (benchTwoByteStrings <$> [ AppendByteString ])
                   <> [benchConsByteString]
                   <> (benchByteStringNoArgOperations <$> [ LengthOfByteString ])
                   <> [benchIndexByteString gen]
                   <> [benchSliceByteString]
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
