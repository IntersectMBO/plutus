{- | Benchmarks for string builtins.  Remember that "strings" are actually Text. -}

module Benchmarks.Strings (makeBenchmarks) where

import           Benchmarks.Common

import           PlutusCore                             as PLC
import           PlutusCore.Evaluation.Machine.ExMemory

import           Criterion.Main
import           Data.ByteString                        as BS
import           Data.Functor                           ((<&>))
import qualified Data.Text                              as T
import qualified Data.Text.Encoding                     as T
import           System.Random                          (StdGen)

import qualified Hedgehog                               as H
import qualified Hedgehog.Internal.Gen                  as G
import qualified Hedgehog.Range                         as R

import qualified Debug.Trace                            as T

{- The memory usage of a string is defined to be four bytes per character.  Plutus
 strings are implemented as Text objects, which are UTF-16 encoded sequences of
 Unicode characters.  For characters (by which Text means codepoints) in the
 Basic Multilingual Plane, UTF-16 requires two bytes, and for other planes four
 bytes (and the actual codepoint for these is obtained by extracting certain
 bits from the two 16-bit parts of the encoding).  The characters we'll
 encounter in practice will probably all be in the BMP (perhaps with the
 exception of emoji), but we still allow one word per character, the number of
 characters being given by 'Data.Text.length'.  For benchmarking it's not
 entirely clear what sort of strings we should provide as input: strings of
 two-byte characters or strings of four-byte characters.  Four-byte characters
 may require some extra processing by certain functions, so we use those as
 input in order to get worst-case behaviour.  This may overestimate costs for
 the strings we encounter in practice.
-}

seedA :: H.Seed
seedA = H.Seed 42 43

seedB :: H.Seed
seedB = H.Seed 44 45

stringSizesSmall :: [Integer]
stringSizesSmall = [0, 5..100]

stringSizesMedium :: [Integer]
stringSizesMedium = [0, 10..1000]

stringSizesBig :: [Integer]
stringSizesBig = [0, 200..10000]

makeSizedString :: H.Seed -> Int -> T.Text
makeSizedString seed n = genSample seed (G.text (R.singleton n) G.unicode)

-- We use the unicode generator here: this will typically give us characters
-- that require four bytes in UTF-16 format. What is the size here?  Number
-- of bytes or number of characters?  Suppose we let u = utf8 (Range.singleton
-- 100).  The number 100 here is the number of Unicode characters in the output
-- of the generator.  If we look at (u ascii) it always gives us a bytestring of
-- length 100; (u latin1) gives bytestrings of length ~ 140-160; (u unicode)
-- gives bytestrings of length ~ 390-400.  Applying decodeUtf8, the output of
-- all of these yields Text strings of length 100.
-- UTF-16: two bytes in the BMP, four in the other planes.
makeSizedUtf8ByteString :: H.Seed -> Int -> BS.ByteString
makeSizedUtf8ByteString seed e = genSample seed (G.utf8 (R.singleton (4*e)) G.unicode)
-- 4*e because with the unicode generator this will generally produce a
-- bytestring containing e bytes since the *output* will contain 100 characters.

stringsToBench :: H.Seed -> [T.Text]
stringsToBench seed = (makeSizedString seed . fromInteger) <$> stringSizesMedium

utf8StringsToBench :: H.Seed -> [BS.ByteString]
utf8StringsToBench seed = (makeSizedUtf8ByteString seed . fromInteger) <$> stringSizesMedium

benchOneString :: DefaultFun -> Benchmark
benchOneString name =
    createOneTermBuiltinBench name $ stringsToBench seedA

{- This is for DecodeUtf8.  That fails if the encoded data is invalid, so we
   create some valid data for it by encoding random strings. We should use the
   Hedgehog generator for this. -}
benchOneByteString :: DefaultFun -> Benchmark
benchOneByteString name =
    createOneTermBuiltinBench name $ utf8StringsToBench seedA

benchTwoStrings :: DefaultFun -> Benchmark
benchTwoStrings name =
    let s1 = stringsToBench seedA
        s2 = stringsToBench seedB
    in createTwoTermBuiltinBench name s1 s2

benchStringNoArgOperations :: DefaultFun -> Benchmark
benchStringNoArgOperations name =
    bgroup (show name) $
        stringsToBench seedA <&> (\x -> benchDefault (showMemoryUsage x) $ mkApp1 name x)

-- Copy the bytestring here, because otherwise it'll be exactly the same, and the equality will short-circuit.
benchSameTwoStrings :: DefaultFun -> Benchmark
benchSameTwoStrings name = createTwoTermBuiltinBenchElementwise name (stringsToBench seedA)
                               (fmap T.copy $ stringsToBench seedA)

makeBenchmarks :: StdGen -> [Benchmark]
makeBenchmarks _gen = [ benchOneString EncodeUtf8
                      , benchOneByteString DecodeUtf8
                      , benchTwoStrings AppendString
                      , benchSameTwoStrings EqualsString
                      ]



{- TODO:
   appendString
   equalsString
   encodeUtf8
   decodeUtf8
-}
