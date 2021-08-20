{- | Benchmarks for string builtins.  Remember that "strings" are actually Text. -}

module Benchmarks.Strings (makeBenchmarks) where

import           Benchmarks.Common

import           PlutusCore                             as PLC
import           PlutusCore.Evaluation.Machine.ExMemory

import           Criterion.Main
import           Data.Functor                           ((<&>))
import qualified Data.Text                              as T
import qualified Data.Text.Encoding                     as T
import           System.Random                          (StdGen)

import qualified Hedgehog                               as HH
import qualified Hedgehog.Internal.Gen                  as HH
import qualified Hedgehog.Internal.Tree                 as HH
import qualified Hedgehog.Range                         as HH.Range

import qualified Debug.Trace                            as T

stringSizes1 :: [Integer]
stringSizes1 = [0, 5..100]

stringSizes1a :: [Integer]
stringSizes1a = [0, 10..1000]

stringSizes2 :: [Integer]
stringSizes2 = [0, 200..10000]

makeSizedString :: HH.Seed -> Int -> (T.Text, ExMemory)
makeSizedString seed e = let x = genSample seed (HH.text (HH.Range.singleton e) HH.unicode) in (x, memoryUsage x)

stringsToBench :: HH.Seed -> [(T.Text, ExMemory)]
stringsToBench seed = (makeSizedString seed . fromInteger) <$> stringSizes1a

seedA :: HH.Seed
seedA = HH.Seed 42 43

seedB :: HH.Seed
seedB = HH.Seed 44 45

benchOneString :: DefaultFun -> Benchmark
benchOneString name =
    createOneTermBuiltinBench name (stringsToBench seedA)

{- This is for DecodeUtf8.  That fails if the encoded data is invalid,
   so we create some valid data for it by encoding random strings. -}
benchOneByteString :: DefaultFun -> Benchmark
benchOneByteString name =
    createOneTermBuiltinBench name $ map toByteString (stringsToBench seedA)
        where toByteString (s,_) = let b = T.encodeUtf8 s in (b, memoryUsage b)

benchTwoStrings :: DefaultFun -> Benchmark
benchTwoStrings name =
    let s1 = stringsToBench seedA
        s2 = stringsToBench seedB
    in createTwoTermBuiltinBench name s1 s2

benchStringNoArgOperations :: DefaultFun -> Benchmark
benchStringNoArgOperations name =
    bgroup (show name) $
        stringsToBench seedA <&> (\(x, xmem) -> benchDefault (show xmem) $ mkApp1 name x)

-- Copy the bytestring here, because otherwise it'll be exactly the same, and the equality will short-circuit.
benchSameTwoStrings :: DefaultFun -> Benchmark
benchSameTwoStrings name = createTwoTermBuiltinBenchElementwise name (stringsToBench seedA)
                               ((\(s, e) -> (T.copy s, e)) <$> stringsToBench seedA)

makeBenchmarks :: StdGen -> [Benchmark]
makeBenchmarks _gen = [  -- benchOneString EncodeUtf8
                         benchOneByteString DecodeUtf8
--                      , benchTwoStrings AppendString
--                      , benchSameTwoStrings EqualsString
                      ]



{- TODO:
   appendString
   equalsString
   encodeUtf8
   decodeUtf8
-}
