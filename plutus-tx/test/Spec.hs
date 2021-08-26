{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications  #-}
module Main(main) where

import qualified Codec.CBOR.FlatTerm as FlatTerm
import           Codec.Serialise     (deserialiseOrFail, serialise)
import qualified Codec.Serialise     as Serialise
import qualified Data.ByteString     as BS
import           Data.Either         (isLeft)
import           Hedgehog            (MonadGen, Property, PropertyT, annotateShow, assert, forAll, property, tripping)
import qualified Hedgehog.Gen        as Gen
import qualified Hedgehog.Range      as Range
import           PlutusCore.Data     (Data (..))
import           PlutusTx.List       (nub, nubBy)
import           PlutusTx.Numeric    (negate)
import           PlutusTx.Prelude    (dropByteString, takeByteString)
import           PlutusTx.Ratio      (Rational, denominator, numerator, recip, (%))
import           PlutusTx.Sqrt       (Sqrt (..), isqrt, rsqrt)
import           Prelude             hiding (Rational, negate, recip)
import           Test.Tasty
import           Test.Tasty.HUnit    (testCase, (@?=))
import           Test.Tasty.Hedgehog (testProperty)

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "plutus-tx" [
    serdeTests
    , sqrtTests
    , ratioTests
    , bytestringTests
    , listTests
    ]

sqrtTests :: TestTree
sqrtTests = testGroup "isqrt/rsqrt tests"
  [ testProperty "isqrt x^2 = x" isqrtRoundTrip
  , testProperty "rsqrt (a/b)^2 = integer part of a/b" rsqrtRoundTrip
  , testProperty "rsqrt (-x/b) = Imaginary" rsqrtRoundTripImaginary
  ]

rsqrtRoundTripImaginary :: Property
rsqrtRoundTripImaginary = property $ do
  let numerators   = Gen.integral (Range.linear (-100000) 0)
  let denominators = Gen.integral (Range.linear 1 100000)

  -- Note: We're using the fact that (a % -b) is reduced to (-a % b)
  -- so we only need to test those negative numbers.

  a <- forAll numerators
  b <- forAll denominators

  let x      = a % b
      decode = \case
            Imaginary -> True
            _         -> False

  assert $ decode (rsqrt x)

rsqrtRoundTrip :: Property
rsqrtRoundTrip = property $ do
  let numerators   = Gen.integral (Range.linear 0 100000)
  let denominators = Gen.integral (Range.linear 1 100000)

  a <- forAll numerators
  b <- forAll denominators

  let x = a % b
      f = square
      g = decode . rsqrt
      integerPart = a `div` b
      remainder = rem a b
      decode = \case
            Exactly       i -> i == integerPart && remainder == 0
            Approximately i -> i == integerPart && remainder > 0
            Imaginary       -> False

  assert $ g (f x)

square :: Rational -> Rational
square r =
  let
    n = numerator r
    d = denominator r
    two = 2 :: Integer
    in (n^two) % (d^two)

isqrtRoundTrip :: Property
isqrtRoundTrip = property $ do
  let positiveInteger = Gen.integral (Range.linear 0 100000)
  x' <- forAll positiveInteger
  tripping x' sq (decodeExact . isqrt)
    where
      sq x = x ^ (2 :: Integer)
      decodeExact (Exactly x) = Right x
      decodeExact s           = Left  s

serdeTests :: TestTree
serdeTests = testGroup "Data serialisation"
    [ testProperty "data round-trip" dataRoundTrip
    , testProperty "no big bytestrings" noBigByteStrings
    , testProperty "no big integers" noBigIntegers
    ]

dataRoundTrip :: Property
dataRoundTrip = property $ do
    dt :: Data <- forAll genData
    let res = deserialiseOrFail (serialise dt)
    annotateShow res

    -- Debugging info
    let ft = FlatTerm.toFlatTerm $ Serialise.encode dt
    annotateShow ft
    annotateShow $ FlatTerm.validFlatTerm ft
    assert (res == Right dt)

sixtyFourByteInteger :: Integer
sixtyFourByteInteger = 2^((64 :: Integer) *8)

genData :: MonadGen m => m Data
genData =
    let st = Gen.subterm genData id
        positiveInteger = Gen.integral (Range.linear 0 100000)
        reasonableInteger = Gen.integral (Range.linear (-100000) 100000)
        -- over 64 bytes
        reallyBigInteger = Gen.integral (Range.linear sixtyFourByteInteger (sixtyFourByteInteger * 2))
        reallyBigNInteger = Gen.integral (Range.linear (-(sixtyFourByteInteger * 2)) (-sixtyFourByteInteger))
        -- includes > 64bytes
        someBytes = Gen.bytes (Range.linear 0 256)
        constructorArgList = Gen.list (Range.linear 0 50) st
        kvMapList = Gen.list (Range.linear 0 50) ((,) <$> st <*> st)
    in
    Gen.recursive Gen.choice
        [ I <$> reasonableInteger
        , I <$> reallyBigInteger
        , I <$> reallyBigNInteger
        , B <$> someBytes ]
        [ Constr <$> positiveInteger <*> constructorArgList
        , List <$> constructorArgList
        , Map <$> kvMapList
        ]

noBigByteStrings :: Property
noBigByteStrings = property $ do
    -- Our serializer for Data is too clever to make big bytestrings, so we serialize a bytestring directly
    -- and try to decode it as Data
    dt :: BS.ByteString <- forAll $ Gen.bytes (Range.linear 65 256)
    annotateShow dt
    let res :: Either Serialise.DeserialiseFailure Data = deserialiseOrFail (serialise dt)
    annotateShow res
    assert (isLeft res)

noBigIntegers :: Property
noBigIntegers = property $ do
    -- Our serializer for Data is too clever to make big integers, so we serialize a bytestring directly
    -- and try to decode it as Data
    dt :: Integer <- forAll $ Gen.integral (Range.linear sixtyFourByteInteger (sixtyFourByteInteger * 2))
    annotateShow dt
    let res :: Either Serialise.DeserialiseFailure Data = deserialiseOrFail (serialise dt)
    annotateShow res
    assert (isLeft res)

ratioTests :: TestTree
ratioTests = testGroup "Ratio"
  [ testProperty "reciprocal ordering 1" reciprocalOrdering1
  , testProperty "reciprocal ordering 2" reciprocalOrdering2
  , testProperty "reciprocal ordering 3" reciprocalOrdering3
  ]

genPositiveRational :: Monad m => PropertyT m Rational
genPositiveRational = do
  a <- forAll . Gen.integral $ Range.linear 1 100000
  b <- forAll . Gen.integral $ Range.linear 1 100000
  return (a % b)

genNegativeRational :: Monad m => PropertyT m Rational
genNegativeRational = negate <$> genPositiveRational

-- If x and y are positive rational numbers and x < y then 1/y < 1/x
reciprocalOrdering1 :: Property
reciprocalOrdering1 = property $ do
  x <- genPositiveRational
  y <- genPositiveRational
  if x < y
  then assert (recip y < recip x)
  else if y < x
  then assert (recip x < recip y)
  else return ()

-- If x and y are negative rational numbers and x < y then 1/y < 1/x
reciprocalOrdering2 :: Property
reciprocalOrdering2 = property $ do
  x <- genNegativeRational
  y <- genNegativeRational
  if x < y
  then assert (recip y < recip x)
  else if y < x
  then assert (recip x < recip y)
  else return ()

-- If x is a negative rational number and y is a positive rational number
-- then 1/x < 1/y
reciprocalOrdering3 :: Property
reciprocalOrdering3 = property $ do
  x <- genNegativeRational
  y <- genPositiveRational
  assert (recip x < recip y)

bytestringTests :: TestTree
bytestringTests = testGroup "ByteString"
  [ takeByteStringTests
  , dropByteStringTests
  ]

takeByteStringTests :: TestTree
takeByteStringTests = testGroup "takeByteString"
  [ testCase "take 0" $ takeByteString 0 "hello" @?= ""
  , testCase "take 1" $ takeByteString 1 "hello" @?= "h"
  , testCase "take 3" $ takeByteString 3 "hello" @?= "hel"
  , testCase "take 10" $ takeByteString 10 "hello" @?= "hello"
  ]

dropByteStringTests :: TestTree
dropByteStringTests = testGroup "dropByteString"
  [ testCase "drop 0" $ dropByteString 0 "hello" @?= "hello"
  , testCase "drop 1" $ dropByteString 1 "hello" @?= "ello"
  , testCase "drop 3" $ dropByteString 3 "hello" @?= "lo"
  , testCase "drop 10" $ dropByteString 10 "hello" @?= ""
  ]

listTests :: TestTree
listTests = testGroup "List"
  [ nubByTests
  , nubTests
  ]

nubByTests :: TestTree
nubByTests = testGroup "nubBy"
  [ testCase "equal up to mod 3" $ nubBy (\x y -> mod x 3 == mod y 3) [1 :: Integer,2,4,5,6] @?= [1,2,6]
  ]

nubTests :: TestTree
nubTests = testGroup "nub"
  [ testCase "[] == []" $ nub [] @?= ([] :: [Integer])
  , testCase "[1, 2, 2] == [1, 2]" $ nub [1 :: Integer, 2, 2] @?= [1, 2]
  , testCase "[2, 1, 1] == [2, 1]" $ nub [2 :: Integer, 1, 1] @?= [2, 1]
  , testCase "[1, 1, 1] == [1]" $ nub [1 :: Integer, 1, 1] @?= [1]
  , testCase "[1, 2, 3, 4, 5] == [1, 2, 3, 4, 5]" $ nub [1 :: Integer, 2, 3, 4, 5] @?= [1, 2, 3, 4, 5]
  ]
