module Benchmarks.ByteStrings (makeBenchmarks) where

import           Benchmarks.Common

import           PlutusCore                             as PLC
import           PlutusCore.Evaluation.Machine.ExMemory

import           Criterion.Main
import qualified Data.ByteString                        as BS
import           Data.Functor                           ((<&>))
import           System.Random                          (StdGen, randomR)

import qualified Hedgehog                               as HH
import qualified Hedgehog.Internal.Gen                  as HH
import qualified Hedgehog.Range                         as HH.Range


---------------- ByteString builtins ----------------

byteStringSizes :: [Integer]
byteStringSizes = integerPower 2 <$> [1..20::Integer]

makeSizedByteString :: HH.Seed -> Int -> (BS.ByteString, ExMemory)
makeSizedByteString seed e = let x = genSample seed (HH.bytes (HH.Range.singleton e)) in (x, memoryUsage x)

byteStringsToBench :: HH.Seed -> [(BS.ByteString, ExMemory)]
byteStringsToBench seed = (makeSizedByteString seed . fromInteger) <$> byteStringSizes

seedA :: HH.Seed
seedA = HH.Seed 42 43

seedB :: HH.Seed
seedB = HH.Seed 44 45

benchTwoByteStrings :: DefaultFun -> Benchmark
benchTwoByteStrings name = createTwoTermBuiltinBench name (byteStringsToBench seedA) (byteStringsToBench seedB)

benchByteStringNoArgOperations :: DefaultFun -> Benchmark
benchByteStringNoArgOperations name =
    bgroup (show name) $
        byteStringsToBench seedA <&> (\(x, xmem) -> benchDefault (show xmem) $ mkApp1 name x)

-- Copy the byteString here, because otherwise it'll be exactly the same, and the equality will short-circuit.
benchSameTwoByteStrings :: DefaultFun -> Benchmark
benchSameTwoByteStrings name = createTwoTermBuiltinBenchElementwise name (byteStringsToBench seedA)
                               ((\(bs, e) -> (BS.copy bs, e)) <$> byteStringsToBench seedA)

benchIndexByteString :: StdGen -> Benchmark
benchIndexByteString gen = createTwoTermBuiltinBenchElementwise IndexByteString (byteStringsToBench seedA) numbers
    where
        numbers = map (\s -> let x = fst $ randomR (0, s - 1) gen in (x, memoryUsage x)) byteStringSizes

benchSliceByteString :: StdGen -> Benchmark
benchSliceByteString gen = bgroup (show SliceByteString) $
    zipWith (\(b, bmem) (from, to) -> bgroup (show bmem) [mkBM b from to]) (byteStringsToBench seedA) indices
    where
        numbers = map (\s -> fst $ randomR (1, s - 1) gen) byteStringSizes
        indices = map (\to -> let from = fst $ randomR (0, to) gen in (from, to)) numbers
        mkBM b from to = bgroup (show $ memoryUsage from) $
            [benchDefault (show $ memoryUsage to) $ mkApp3 SliceByteString from to b]

benchByteStringOperations :: DefaultFun -> Benchmark -- TODO the numbers are a bit too big here
benchByteStringOperations name = createTwoTermBuiltinBench name numbers (byteStringsToBench seedA)
    where
        numbers = threeToThePower <$> powersOfTwo

makeBenchmarks :: StdGen -> [Benchmark]
makeBenchmarks gen =  (benchTwoByteStrings <$> [ AppendByteString ])
                   <> (benchByteStringOperations <$> [ ConsByteString ])
                   <> [benchIndexByteString gen]
                   <> [benchSliceByteString gen]
                   <> (benchByteStringNoArgOperations <$> [ LengthOfByteString ])
                   <> (benchSameTwoByteStrings <$> [ EqualsByteString, LessThanByteString ])

-- TODO: LessThanEqualsByteString
