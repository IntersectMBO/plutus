module Main (main) where

import           Data.MonoTraversable
import           Data.Vector
import           Data.Word
import           Data.Word64Array.Word8 as WordArray
import           Test.QuickCheck
import           Test.Tasty
import           Test.Tasty.QuickCheck

toVector :: WordArray -> Vector Word8
toVector = fromList . WordArray.toList

instance Arbitrary WordArray where
    arbitrary = toWordArray <$> arbitrary
    shrink (WordArray w) = WordArray <$> shrink w

instance Arbitrary Index where
    arbitrary = Index <$> choose (0, 7)
    shrink (Index i) = if i == 0 then [] else [Index (i-1)]

main :: IO ()
main = defaultMain $
    testGroup "word-array" [
        testProperty "write" $ \(arr, ix@(Index i), w8) ->
            toVector (writeArray arr ix w8) == toVector arr // [(i, w8)]
        , testProperty "read" $ \(arr, ix@(Index i)) ->
            readArray arr ix == toVector arr ! i
        , testProperty "fold" $ \arr ->
            ofoldr (+) 0 arr == Prelude.foldr (+) 0 (toVector arr)
    ]
