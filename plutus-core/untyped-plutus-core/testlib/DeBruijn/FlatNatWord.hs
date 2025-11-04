{-# LANGUAGE LambdaCase       #-}
{-# LANGUAGE TypeApplications #-}
-- | Check compatibility of Flat Natural to Flat Word64
-- needed for Index (de)serialization see Note [DeBruijn Index serialization]
module DeBruijn.FlatNatWord (test_flatNatWord) where

import PlutusCore.DeBruijn
import PlutusCore.FlatInstances ()

import Data.Either (isLeft)
import Data.Word
import GHC.Natural
import Hedgehog
import Hedgehog.Gen qualified as Gen
import Hedgehog.Range qualified as Range
import PlutusCore.Flat
import PlutusCore.Flat.Encoder
import Test.Tasty
import Test.Tasty.Extras
import Test.Tasty.Hedgehog
import Test.Tasty.HUnit

-- test that Natural and Word64 are compatible inside
-- the (minBound,maxBound) bounds of Word64
prop_CompatInBounds :: TestTree
prop_CompatInBounds = testProperty "compatible inside bounds" $ property $ do
    -- test that their encodings are byte-to-byte the same
    w <- forAll $ Gen.word64 Range.linearBounded
    let n :: Natural = fromIntegral w
    flat w === flat n

    -- Tripping from encoded as natural to decoded as word
    tripping w (flat @Natural . fromIntegral) unflat

    -- Tripping from encoded as word to decoded as natural
    tripping n (flat @Word64 . fromIntegral) unflat

prop_DecLarger :: TestTree
prop_DecLarger = testProperty "dec outside bounds" $ property $ do
    n <- forAll $ Gen.integral $ Range.linear (maxWord64AsNat+1) (maxWord64AsNat*10)
    Hedgehog.assert $ isLeft $ unflat @Word64 $ flat @Natural n

test_MinBound :: TestTree
test_MinBound = testCase "compatible minbound" $ do
    let w = minBound @Word64
        n :: Natural = fromIntegral w
    flat w == flat n @? "enc minbound does not match"
    -- Tripping from encoded as natural to decoded as word
    Right w == (unflat $ flat n)  @? "tripping1 minbound failed"
    -- Tripping from encoded as word to decoded as natural
    Right n == (unflat $ flat w) @? "tripping1 minbound failed"

test_MaxBound :: TestTree
test_MaxBound = testCase "compatible maxbound" $ do
    let w = maxBound @Word64
        n :: Natural = fromIntegral w
    flat w == flat n @? "enc maxbound does not match"
    -- Tripping from encoded as natural to decoded as word
    Right w == (unflat $ flat n)  @? "tripping1 maxbound failed"
    -- Tripping from encoded as word to decoded as natural
    Right n == (unflat $ flat w) @? "tripping1 maxbound failed"


prop_OldVsNewIndex :: TestTree
prop_OldVsNewIndex = testProperty "oldVsNew Index" $ property $ do
    n <- forAll $ Gen.integral $ Range.linear minWord64AsNat (maxWord64AsNat*10)
    let encoded = flat @Natural n
        isCompatible = curry $ \case
            (Right (Index newDecoded), Right (OldIndex oldDecoded)) -> newDecoded == oldDecoded
            (Left _, Left _)                                        -> True
            _                                                       -> False

    Hedgehog.assert $ unflat @Index encoded `isCompatible` unflat @OldIndex encoded

test_flatNatWord :: TestNested
test_flatNatWord =
    testNested "FlatNatWord" $ map embed
        [ test_MinBound
        , test_MaxBound
        , prop_CompatInBounds
        , prop_DecLarger
        , prop_OldVsNewIndex
        ]

-- * Old implementation of Flat Index copy-pasted and renamed to OldIndex

{- |
The old implementation relied on this function which is safe
*only* for 64-bit systems. There were previously safety checks to fail compilation
on other systems, but we removed them  since we only test on 64-bit systems afterall.
-}
naturalToWord64Maybe :: Natural -> Maybe Word64
naturalToWord64Maybe n = fromIntegral <$> naturalToWordMaybe n
{-# INLINABLE naturalToWord64Maybe #-}

newtype OldIndex = OldIndex {unOldIndex :: Word64}
  deriving stock (Generic)
  deriving newtype (Show, Num, Enum, Ord, Real, Integral, Eq)

instance Flat OldIndex where
    -- encode from word64 to natural
    encode = encode @Natural . fromIntegral
    -- decode from natural to word64
    decode = do
        n <- decode @Natural
        case naturalToWord64Maybe n of
            Nothing  -> fail $ "Index outside representable range: " ++ show n
            Just w64 -> pure $ OldIndex w64
    -- to be exact, we must not let this be generically derived,
    -- because the `gsize` would derive the size of the underlying Word64,
    -- whereas we want the size of Natural
    size = sNatural . fromIntegral


-- * helpers

minWord64AsNat :: Natural
minWord64AsNat = fromIntegral @Word64 @Natural minBound

maxWord64AsNat :: Natural
maxWord64AsNat = fromIntegral @Word64 @Natural maxBound
