module Test.LargeInteger (testLargeIntegers) where

import Data.Bits (shiftL)
import Data.ByteString qualified as B
import Data.Either (isLeft)
import Numeric.Natural (Natural)
import PlutusCore.Flat (Decoded, Flat, flat, unflat, unflatRaw)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertBool, testCase, (@?=))

testLargeIntegers :: TestTree
testLargeIntegers =
  testGroup
    "large integers"
    [ testGroup "roundtrip around bit boundaries" $ fmap boundaryTests boundaryExponents
    , testGroup "explicit long encodings" $ fmap explicitEncodingTests encodedChunkCounts
    , testGroup "explicit long Natural encodings" $
        fmap explicitNaturalEncodingTest naturalChunkCounts
    , testGroup
        "accepted redundant high zero chunks"
        [ testCase "two-chunk zero" $
            decodeRawInteger (B.pack [0x80, 0x00]) @?= Right 0
        , testCase "4097-chunk zero" $
            decodeRawInteger (B.replicate 4096 0x80 <> B.singleton 0x00) @?= Right 0
        , testCase "redundant zero after a 1024-chunk positive power" $
            decodeRawInteger (overlongPositivePowerEncoding 1024)
              @?= Right ((1 :: Integer) `shiftL` (7 * 1023))
        ]
    , testGroup
        "all bit offsets"
        ( fmap offsetRoundtripTest [0 .. 7]
            ++ [ testCase "large positive Integer and Natural between Bools" $
                   assertRoundtrip (True, largePositiveInteger, largeNatural, False)
               , testCase "large negative Integer and Natural between Bools" $
                   assertRoundtrip (False, negate largePositiveInteger, largeNatural, True)
               ]
        )
    , testGroup
        "malformed long encodings"
        [ testCase "empty input" $
            assertDecodeFailure B.empty
        , testCase "4096 nonzero continuation chunks without a terminator" $
            assertDecodeFailure (B.replicate 4096 0x81)
        , testCase "valid 1024-chunk integer followed by an extra byte" $
            assertDecodeFailure (positivePowerEncoding 1024 <> B.singleton 0)
        ]
    ]

-- These straddle both Flat's seven-bit chunk boundaries and common machine-word
-- boundaries, and extend far enough to exercise a genuinely multi-limb Integer.
boundaryExponents :: [Int]
boundaryExponents =
  [ 0
  , 1
  , 5
  , 6
  , 7
  , 8
  , 12
  , 13
  , 14
  , 15
  , 31
  , 32
  , 33
  , 62
  , 63
  , 64
  , 127
  , 128
  , 129
  , 1023
  , 4095
  , 16383
  ]

boundaryTests :: Int -> TestTree
boundaryTests exponent =
  let power = (1 :: Integer) `shiftL` exponent
   in testGroup
        ("2^" ++ show exponent)
        [ testCase "positive - 1" $ assertRoundtrip (power - 1)
        , testCase "positive" $ assertRoundtrip power
        , testCase "positive + 1" $ assertRoundtrip (power + 1)
        , testCase "negative - 1" $ assertRoundtrip (negate power - 1)
        , testCase "negative" $ assertRoundtrip (negate power)
        , testCase "negative + 1" $ assertRoundtrip (negate power + 1)
        ]

-- Include boundaries around sizes that are useful in the corresponding
-- Criterion benchmark, without making the correctness suite itself a benchmark.
encodedChunkCounts :: [Int]
encodedChunkCounts =
  [ 1
  , 2
  , 3
  , 9
  , 10
  , 18
  , 19
  , 31
  , 32
  , 33
  , 63
  , 64
  , 65
  , 127
  , 128
  , 129
  , 1024
  , 4096
  ]

explicitEncodingTests :: Int -> TestTree
explicitEncodingTests chunks =
  let magnitude = (1 :: Integer) `shiftL` (7 * (chunks - 1))
   in testGroup
        (show chunks ++ " chunks")
        [ testCase "positive power" $
            decodeRawInteger (positivePowerEncoding chunks) @?= Right magnitude
        , testCase "negative power" $
            decodeRawInteger (negativePowerEncoding chunks) @?= Right (negate magnitude)
        ]

naturalChunkCounts :: [Int]
naturalChunkCounts = [1, 2, 10, 18, 19, 31, 32, 33, 63, 64, 65, 128, 1024, 4096]

explicitNaturalEncodingTest :: Int -> TestTree
explicitNaturalEncodingTest chunks =
  let expected = (1 :: Natural) `shiftL` (7 * (chunks - 1) + 1) - 1
   in testCase (show chunks ++ " nonzero chunks") $
        decodeRawNatural (negativePowerEncoding chunks) @?= Right expected

-- Both values occupy 4096 seven-bit chunks.  Placing them after a Bool keeps
-- every dWord8 call at a one-bit offset; the trailing Bool also checks that the
-- decoder leaves the bit state at the correct position.
largePositiveInteger :: Integer
largePositiveInteger = (1 :: Integer) `shiftL` (7 * 4096 - 1) - 1

largeNatural :: Natural
largeNatural = (1 :: Natural) `shiftL` (7 * 4096) - 1

offsetRoundtripTest :: Int -> TestTree
offsetRoundtripTest prefixLength =
  let bitOffset = (prefixLength + 1) `mod` 8
      integer =
        if even prefixLength
          then largePositiveInteger
          else negate largePositiveInteger
   in testCase ("bit offset " ++ show bitOffset) $
        assertRoundtrip (replicate prefixLength (), integer, largeNatural)

-- ZigZag encodes +2^(7*(chunks-1)) as the unsigned value
-- 2 * 128^(chunks-1), whose little-endian base-128 digits are all zero except
-- for the final digit 2.
positivePowerEncoding :: Int -> B.ByteString
positivePowerEncoding chunks =
  B.replicate (chunks - 1) 0x80 <> B.singleton 0x02

overlongPositivePowerEncoding :: Int -> B.ByteString
overlongPositivePowerEncoding chunks =
  B.replicate (chunks - 1) 0x80 <> B.pack [0x82, 0x00]

-- ZigZag encodes -2^(7*(chunks-1)) as 2 * 128^(chunks-1) - 1, whose payload
-- digits are [127, ..., 127, 1].  This also exercises a nonzero payload in
-- every chunk, which is the worst case for a shift-and-OR decoder.
negativePowerEncoding :: Int -> B.ByteString
negativePowerEncoding chunks =
  B.replicate (chunks - 1) 0xff <> B.singleton 0x01

assertRoundtrip :: (Eq a, Flat a, Show a) => a -> IO ()
assertRoundtrip value =
  unflat (flat value :: B.ByteString) @?= Right value

decodeRawInteger :: B.ByteString -> Decoded Integer
decodeRawInteger = unflatRaw

decodeRawNatural :: B.ByteString -> Decoded Natural
decodeRawNatural = unflatRaw

assertDecodeFailure :: B.ByteString -> IO ()
assertDecodeFailure encoded =
  assertBool "expected integer decoding to fail" $ isLeft (decodeRawInteger encoded)
