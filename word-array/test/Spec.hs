{-# OPTIONS_GHC -Wno-orphans #-}
module Main (main) where

import Data.MonoTraversable
import Data.Vector
import Data.WideWord
import Data.Word
import Data.Word128Array.Word8 qualified as WA128
import Data.Word64Array.Word8 qualified as WA64
import Test.QuickCheck
import Test.Tasty
import Test.Tasty.QuickCheck

toVector64 :: WA64.WordArray -> Vector Word8
toVector64 = fromList . WA64.toList

instance Arbitrary WA64.WordArray where
    arbitrary = WA64.toWordArray <$> arbitrary
    shrink (WA64.WordArray w) = WA64.WordArray <$> shrink w

instance Arbitrary WA64.Index where
    arbitrary = WA64.Index <$> choose (0, 7)
    shrink (WA64.Index i) = if i == 0 then [] else [WA64.Index (i-1)]

toVector128 :: WA128.WordArray -> Vector Word8
toVector128 = fromList . WA128.toList

instance Arbitrary Word128 where
    arbitrary = fromInteger <$> arbitrary

instance Arbitrary WA128.WordArray where
    arbitrary = WA128.toWordArray <$> arbitrary
    shrink (WA128.WordArray w) = WA128.WordArray <$> shrink w

instance Arbitrary WA128.Index where
    arbitrary = WA128.Index <$> choose (0, 7)
    shrink (WA128.Index i) = if i == 0 then [] else [WA128.Index (i-1)]

main :: IO ()
main = defaultMain $
    testGroup "word-array" [
        testGroup "Word64/Word8" [
            testProperty "write" $ \(arr, ix@(WA64.Index i), w8) ->
                toVector64 (WA64.writeArray arr ix w8) == toVector64 arr // [(i, w8)]
            , testProperty "read" $ \(arr, ix@(WA64.Index i)) ->
                WA64.readArray arr ix == toVector64 arr ! i
            , testProperty "fold" $ \arr ->
                ofoldr (+) 0 arr == Prelude.foldr (+) 0 (toVector64 arr)
        ]
        , testGroup "Word128/Word8" [
            testProperty "write" $ \(arr, ix@(WA128.Index i), w8) ->
                toVector128 (WA128.writeArray arr ix w8) == toVector128 arr // [(i, w8)]
            , testProperty "read" $ \(arr, ix@(WA128.Index i)) ->
                WA128.readArray arr ix == toVector128 arr ! i
            , testProperty "fold" $ \arr ->
                ofoldr (+) 0 arr == Prelude.foldr (+) 0 (toVector128 arr)
        ]
    ]
