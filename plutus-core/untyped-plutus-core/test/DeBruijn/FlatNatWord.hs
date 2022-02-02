{-# LANGUAGE TypeApplications #-}
module DeBruijn.FlatNatWord (test_flatNatWord) where

import Data.Either (isLeft)
import Data.Word
import Flat
import Numeric.Natural
import PlutusCore.Flat ()

import Hedgehog
import Hedgehog.Gen qualified as Gen
import Hedgehog.Range qualified as Range
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.Hedgehog



{- NOTE: [DeBruijjn index flat format]
In the debruijn branch we are transitioning the debruijn index to be a Word instead of Natural, for CEK performance reasons.

This means the types of `Script`,`Program`,`Term` change and so does the flat "interface".

This module tests that although the interface/types change,
the underlying flat encoding/decoding remains the same,
so there is no need to issue a new plutus language version increase.
-}

test_flatNatWord :: TestTree
test_flatNatWord = testGroup "FlatNatWord"
    [ testCase "compatible minbound" test_MinBound
    , testCase "compatible maxbound" test_MaxBound
    , testProperty "compatible inside bounds" prop_CompatInBounds
    , testProperty "dec outside bounds" prop_DecLarger
    ]

-- test that Natural and Word64 are compatible inside
-- the (minBound,maxBound) bounds of Word64
prop_CompatInBounds :: Property
prop_CompatInBounds = property $ do
    -- test that their encodings are byte-to-byte the same
    w <- forAll $ Gen.word64 Range.linearBounded
    let n :: Natural = fromIntegral w
    flat w === flat n

    -- Tripping from encoded as natural to decoded as word
    tripping w (flat @Natural . fromIntegral) unflat

    -- Tripping from encoded as word to decoded as natural
    tripping n (flat @Word64 . fromIntegral) unflat

prop_DecLarger :: Property
prop_DecLarger = property $ do
    let maxWord64AsNat = fromIntegral @Word64 @Natural maxBound
    n <- forAll $ Gen.integral $ Range.linear (maxWord64AsNat+1) (maxWord64AsNat*10)
    Hedgehog.assert $ isLeft $ unflat @Word64 $ flat @Natural n

test_MinBound :: Assertion
test_MinBound = do
    let w = minBound @Word64
        n :: Natural = fromIntegral w
    flat w == flat n @? "enc minbound does not match"
    -- Tripping from encoded as natural to decoded as word
    Right w == (unflat $ flat n)  @? "tripping1 minbound failed"
    -- Tripping from encoded as word to decoded as natural
    Right n == (unflat $ flat w) @? "tripping1 minbound failed"

test_MaxBound :: Assertion
test_MaxBound = do
    let w = maxBound @Word64
        n :: Natural = fromIntegral w
    flat w == flat n @? "enc maxbound does not match"
    -- Tripping from encoded as natural to decoded as word
    Right w == (unflat $ flat n)  @? "tripping1 maxbound failed"
    -- Tripping from encoded as word to decoded as natural
    Right n == (unflat $ flat w) @? "tripping1 maxbound failed"
