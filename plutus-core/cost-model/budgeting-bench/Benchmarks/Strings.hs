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

import qualified Hedgehog                               as HH
import qualified Hedgehog.Internal.Gen                  as HH
import qualified Hedgehog.Internal.Tree                 as HH
import qualified Hedgehog.Range                         as HH.Range

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

seedA :: HH.Seed
seedA = HH.Seed 42 43

seedB :: HH.Seed
seedB = HH.Seed 44 45

stringSizesSmall :: [Integer]
stringSizesSmall = [0, 5..100]

stringSizesMedium :: [Integer]
stringSizesMedium = [0, 10..1000]

stringSizesBig :: [Integer]
stringSizesBig = [0, 200..10000]

makeSizedString :: HH.Seed -> Int -> (T.Text, ExMemory)
makeSizedString seed n = let x = genSample seed (HH.text (HH.Range.singleton n) HH.unicode) in (x, memoryUsage x)

-- We use the unicode generator here: this will typically give us characters
-- that require four bytes in UTF-16 format. What is the size here?  Number
-- of bytes or number of characters?  Suppose we let u = utf8 (Range.singleton
-- 100).  The number 100 here is the number of Unicode characters in the output
-- of the generator.  If we look at (u ascii) it always gives us a bytestring of
-- length 100; (u latin1) gives bytestrings of length ~ 140-160; (u unicode)
-- gives bytestrings of length ~ 390-400.  Applying decodeUtf8, the output of
-- all of these yields Text strings of length 100.
-- UTF-16: two bytes in the BMP, four in the other planes.
makeSizedUtf8ByteString :: HH.Seed -> Int -> (BS.ByteString, ExMemory)
makeSizedUtf8ByteString seed e = let x = genSample seed (HH.utf8 (HH.Range.singleton (4*e)) HH.unicode) in (x, memoryUsage x)
-- 4*e because with the unicode generator this will generally produce a
-- bytestring containing e bytes since the *output* will contain 100 characters.

stringsToBench :: HH.Seed -> [(T.Text, ExMemory)]
stringsToBench seed = (makeSizedString seed . fromInteger) <$> stringSizesMedium

utf8StringsToBench :: HH.Seed -> [(BS.ByteString, ExMemory)]
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
        stringsToBench seedA <&> (\(x, xmem) -> benchDefault (show xmem) $ mkApp1 name x)

-- Copy the bytestring here, because otherwise it'll be exactly the same, and the equality will short-circuit.
benchSameTwoStrings :: DefaultFun -> Benchmark
benchSameTwoStrings name = createTwoTermBuiltinBenchElementwise name (stringsToBench seedA)
                               ((\(s, e) -> (T.copy s, e)) <$> stringsToBench seedA)

makeBenchmarks :: StdGen -> [Benchmark]
makeBenchmarks _gen = [  -- benchOneString EncodeUtf8
                         -- benchOneByteString DecodeUtf8
--                      , benchTwoStrings AppendString
--                      , benchSameTwoStrings EqualsString
                      ]



{- TODO:
   appendString
   equalsString
   encodeUtf8
   decodeUtf8
-}
