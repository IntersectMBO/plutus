module Benchmarks.ByteStrings (makeBenchmarks) where

import Common
import Generators
import PlutusBenchmark.Common (EvaluationContext)

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

benchTwoByteStrings :: EvaluationContext -> DefaultFun -> Benchmark
benchTwoByteStrings evalCtx name =
    createTwoTermBuiltinBench name [] (largerByteStrings21 seedA) (largerByteStrings21 seedB)

benchLengthOfByteString :: EvaluationContext -> Benchmark
benchLengthOfByteString evalCtx =
    bgroup (show name) $ fmap mkBM (smallerByteStrings150 seedA)
        where mkBM b = benchDefault (showMemoryUsage b) $ mkApp1 name [] b
              name = LengthOfByteString

-- Copy the byteString here, because otherwise it'll be exactly the same and the equality will
-- short-circuit.
benchSameTwoByteStrings :: EvaluationContext -> DefaultFun -> Benchmark
benchSameTwoByteStrings evalCtx name =
    createTwoTermBuiltinBenchElementwise name [] $ pairWith BS.copy inputs
    where inputs = smallerByteStrings150 seedA

-- Here we benchmark different pairs of bytestrings elementwise.  This is used
-- to get times for off-diagonal comparisons, which we expect to be roughly
-- constant since the equality test returns quickly in that case.
benchDifferentByteStringsElementwise :: EvaluationContext -> DefaultFun -> Benchmark
benchDifferentByteStringsElementwise evalCtx name =
    createTwoTermBuiltinBenchElementwise name [] $ zip inputs1 inputs2
    where inputs1 = smallerByteStrings150 seedA
          inputs2 = smallerByteStrings150 seedB

-- This is constant, even for large inputs
benchIndexByteString :: EvaluationContext -> StdGen -> Benchmark
benchIndexByteString evalCtx gen =
    createTwoTermBuiltinBenchElementwise
        IndexByteString [] $ zip bytestrings (randomIndices gen bytestrings)
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
benchSliceByteString :: EvaluationContext -> Benchmark
benchSliceByteString evalCtx =
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


benchConsByteString :: EvaluationContext -> Benchmark
benchConsByteString evalCtx =
    createTwoTermBuiltinBench ConsByteString [] [n] (smallerByteStrings150 seedA)
        where n = 123 :: Integer
        -- The precise numbers don't seem to matter here, as long as they are in
        -- the range of [0..255] (Word8). Otherwise
        -- we run the risk of costing also the (fast) failures of the builtin call.

makeBenchmarks :: EvaluationContext -> StdGen -> [Benchmark]
makeBenchmarks evalCtx gen =
    [ benchTwoByteStrings evalCtx AppendByteString
    , benchConsByteString evalCtx
    , benchLengthOfByteString evalCtx
    , benchIndexByteString evalCtx gen
    , benchSliceByteString evalCtx
    ]
    <> [benchDifferentByteStringsElementwise evalCtx EqualsByteString]
    <> (benchSameTwoByteStrings evalCtx<$>
         [ EqualsByteString, LessThanEqualsByteString, LessThanByteString ])
