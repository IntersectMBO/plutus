module Main where

import Test.Tasty
import Test.Tasty.HUnit

import Data.Monoid (Sum (..))

import PlutusBenchmark.Values.FlattenedValue qualified as FlattenedValue
import PlutusBenchmark.Values.MMValue qualified as MMValue
import PlutusBenchmark.Values.MockValues
import PlutusBenchmark.Values.NestedValue qualified as NestedValue

testLookupCoin :: TestTree
testLookupCoin =
    testGroup "lookup"
    [ testCase "key exists" $
        let nRes = NestedValue.lookupCoin polId500 tokN999999 nVal1
            fRes = FlattenedValue.lookupCoin polId500 tokN999999 fVal1
            Sum mRes = MMValue.lookupCoin polId500 tokN999999 mVal1
         in assertBool "" (nRes == fRes && fRes == mRes)
    , testCase "key doesn't exist" $ do
        let nRes = NestedValue.lookupCoin polId500 tokN10000 nVal2
            fRes = FlattenedValue.lookupCoin polId500 tokN10000 fVal2
            Sum mRes = MMValue.lookupCoin polId500 tokN10000 mVal2
         in assertBool "" (nRes == fRes && fRes == mRes)
    ]

testInsertCoin :: TestTree
testInsertCoin =
    testGroup "insert"
    [ testCase "key exists" $
        let nRes = NestedValue.toHMap $ NestedValue.insertCoin polId500 tokN999999 200 nVal1
            fRes = FlattenedValue.toHMap $ FlattenedValue.insertCoin polId500 tokN999999 200 fVal1
            mRes = MMValue.toHMap $ MMValue.insertCoin polId500 tokN999999 200 mVal1
         in assertBool "" (nRes == fRes && fRes == mRes)
    , testCase "key doesn't exist" $ do
        let nRes = NestedValue.toHMap $ NestedValue.insertCoin polId500 tokN10000 200 nVal2
            fRes = FlattenedValue.toHMap $ FlattenedValue.insertCoin polId500 tokN10000 200 fVal2
            mRes = MMValue.toHMap $ MMValue.insertCoin polId500 tokN10000 200 mVal2
         in assertBool "" (nRes == fRes && fRes == mRes)
    ]

testDeleteCoin :: TestTree
testDeleteCoin =
    testGroup "delete"
    [ testCase "key exists" $
        let nRes = NestedValue.toHMap $ NestedValue.deleteCoin polId500 tokN999999 nVal1
            fRes = FlattenedValue.toHMap $ FlattenedValue.deleteCoin polId500 tokN999999 fVal1
            mRes = MMValue.toHMap $ MMValue.deleteCoin polId500 tokN999999 mVal1
         in assertBool "" (nRes == fRes && fRes == mRes)
    , testCase "key doesn't exist" $ do
        let nRes = NestedValue.toHMap $ NestedValue.deleteCoin polId500 tokN10000 nVal2
            fRes = FlattenedValue.toHMap $ FlattenedValue.deleteCoin polId500 tokN10000 fVal2
            mRes = MMValue.toHMap $ MMValue.deleteCoin polId500 tokN10000 mVal2
         in assertBool "" (nRes == fRes && fRes == mRes)
    ]

testUnion :: TestTree
testUnion =
    testCase "union" $
        let nRes = NestedValue.toHMap $ NestedValue.union nVal1 nVal2
            fRes = FlattenedValue.toHMap $ FlattenedValue.union fVal1 fVal2
            mRes = MMValue.toHMap $ MMValue.union mVal1 mVal2
         in assertBool "" (nRes == fRes && fRes == mRes)

testContains :: TestTree
testContains =
    testCase "contains" $
        let nRes = NestedValue.valueContains nVal1 nVal2
            fRes = FlattenedValue.valueContains fVal1 fVal2
            mRes = MMValue.valueContains mVal1 mVal2
         in assertBool "" (nRes == fRes && fRes == mRes)

main :: IO ()
main =
    defaultMain
    $ testGroup "plutus-benchmark values tests"
        [ testLookupCoin
        , testInsertCoin
        , testDeleteCoin
        , testUnion
        , testContains
        ]
