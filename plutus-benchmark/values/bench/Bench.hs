{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Data.ByteString (ByteString)
import Data.List (groupBy)
import Data.Map.Strict qualified as Map
import Data.Text qualified as T
import Data.Text.Encoding (encodeUtf8)

import PlutusBenchmark.Common (getConfig)
import PlutusBenchmark.Values.FlattenedValue qualified as FlattenedValue
import PlutusBenchmark.Values.NestedValue qualified as NestedValue

import Criterion.Main (bench, bgroup, defaultMainWith, env, nf)

-- Has been manually tested, works as expected.
mkMockValues :: Int -> Int -> [Integer] -> (NestedValue.Value, FlattenedValue.Value)
mkMockValues numPolicies numToksPerPolicy amounts =
    let policies = (\i -> encodeUtf8 $ "policy" <> T.pack (show i)) <$> [1..numPolicies]
        numTokens = numPolicies * numToksPerPolicy
        tokens = (\i -> encodeUtf8 $ "token" <> T.pack (show i)) <$> [1..numTokens]
        dupPolicies = concatMap (\p -> replicate numToksPerPolicy p) policies
        rawFlatValue :: [((ByteString, ByteString), Integer)]
        rawFlatValue = zip (zip dupPolicies tokens) amounts
        flattenedValue = FlattenedValue.Value $ Map.fromList rawFlatValue
        rawNestValue =
            let x = groupBy (\((p1, _), _) ((p2, _), _) -> p1 == p2) rawFlatValue
             in [ (p, tkMap) | l <- x, let p = (fst . fst) (head l), let tkMap = Map.fromList $ map (\((_, tk), am) -> (tk, am)) l ]
        nestedValue = NestedValue.Value $ Map.fromList rawNestValue
     in (nestedValue, flattenedValue)

mockNumPolicies1 :: Int
mockNumPolicies1 = 10000

mockNumPolicies2 :: Int
mockNumPolicies2 = 5000

mockNumTokensPerPolicy1 :: Int
mockNumTokensPerPolicy1 = 2000

mockNumTokensPerPolicy2 :: Int
mockNumTokensPerPolicy2 = 1000

mockNumTokens1 :: Int
mockNumTokens1 = mockNumPolicies1 * mockNumTokensPerPolicy1

mockNumTokens2 :: Int
mockNumTokens2 = mockNumPolicies2 * mockNumTokensPerPolicy2

mockTokenValues1 :: [Integer]
mockTokenValues1 = replicate mockNumTokens1 200

mockTokenValues2 :: [Integer]
mockTokenValues2 = replicate mockNumTokens2 100

setupEnvNested1 :: IO NestedValue.Value
setupEnvNested1 =
    let (nValue, _) =
            mkMockValues
                mockNumPolicies1
                mockNumTokensPerPolicy1
                mockTokenValues1
     in pure nValue

setupEnvNested2 :: IO (NestedValue.Value, NestedValue.Value)
setupEnvNested2 =
    let (nValue1, _) =
            mkMockValues
                mockNumPolicies1
                mockNumTokensPerPolicy1
                mockTokenValues1
        (nValue2, _) =
            mkMockValues
                mockNumPolicies2
                mockNumTokensPerPolicy2
                mockTokenValues2
     in pure (nValue1, nValue2)

setupEnvFlattened1 :: IO FlattenedValue.Value
setupEnvFlattened1 =
    let (_, fValue) =
            mkMockValues
                mockNumPolicies1
                mockNumTokensPerPolicy1
                mockTokenValues1
     in pure fValue

setupEnvFlattened2 :: IO (FlattenedValue.Value, FlattenedValue.Value)
setupEnvFlattened2 =
    let (_, fValue1) =
            mkMockValues
                mockNumPolicies1
                mockNumTokensPerPolicy1
                mockTokenValues1
        (_, fValue2) =
            mkMockValues
                mockNumPolicies2
                mockNumTokensPerPolicy2
                mockTokenValues2
     in pure (fValue1, fValue2)

setupEnvNested1andInv :: IO (NestedValue.Value, NestedValue.Value)
setupEnvNested1andInv =
    let (nValue1, _) =
            mkMockValues
                mockNumPolicies1
                mockNumTokensPerPolicy1
                mockTokenValues1
        (nValue1Inv, _) =
            mkMockValues
                mockNumPolicies1
                mockNumTokensPerPolicy1
                (map negate mockTokenValues1)
     in pure (nValue1, nValue1Inv)

setupEnvFlattened1andInv :: IO (FlattenedValue.Value, FlattenedValue.Value)
setupEnvFlattened1andInv =
    let (_, fValue1) =
            mkMockValues
                mockNumPolicies1
                mockNumTokensPerPolicy1
                mockTokenValues1
        (_, fValue1Inv) =
            mkMockValues
                mockNumPolicies1
                mockNumTokensPerPolicy1
                (map negate mockTokenValues1)
     in pure (fValue1, fValue1Inv)

main :: IO ()
main = do
    config <- getConfig 30
    defaultMainWith config $
        [ env setupEnvNested1 $ \ ~nValue ->
            bgroup "NestedValue"
                [ bench "insertCoin - new coin"
                    $ nf (NestedValue.insertCoin (encodeUtf8 "policy500") (encodeUtf8 "token10000") 200) nValue
                , bench "insertCoin - existing coin"
                    $ nf (NestedValue.insertCoin (encodeUtf8 "policy500") (encodeUtf8 "token999999") 200) nValue
                , bench "lookupCoin - not found"
                    $ nf (NestedValue.lookupCoin (encodeUtf8 "policy500") (encodeUtf8 "token10000")) nValue
                , bench "lookupCoin - existing coin"
                    $ nf (NestedValue.lookupCoin (encodeUtf8 "policy500") (encodeUtf8 "token999999")) nValue
                , bench "deleteCoin - not found"
                    $ nf (NestedValue.deleteCoin (encodeUtf8 "policy500") (encodeUtf8 "token10000")) nValue
                , bench "deleteCoin - existing coin"
                    $ nf (NestedValue.deleteCoin (encodeUtf8 "policy500") (encodeUtf8 "token999999")) nValue
                , bench "byPolicyId - not found"
                    $ nf (NestedValue.byPolicyId (encodeUtf8 "notHere")) nValue
                , bench "byPolicyId - existing policy"
                    $ nf (NestedValue.byPolicyId (encodeUtf8 "policy500")) nValue
                , bench "byTokenName - not found"
                    $ nf (NestedValue.byTokenName (encodeUtf8 "notHere")) nValue
                , bench "byTokenName - existing token"
                    $ nf (NestedValue.byTokenName (encodeUtf8 "token999999")) nValue
                ]
        , env setupEnvFlattened1 $ \ ~fValue ->
            bgroup "FlattenedValue"
                [ bench "insertCoin - new coin"
                    $ nf (FlattenedValue.insertCoin (encodeUtf8 "policy500") (encodeUtf8 "token10000") 200) fValue
                , bench "insertCoin - existing coin"
                    $ nf (FlattenedValue.insertCoin (encodeUtf8 "policy500") (encodeUtf8 "token999999") 200) fValue
                , bench "lookupCoin - not found"
                    $ nf (FlattenedValue.lookupCoin (encodeUtf8 "policy500") (encodeUtf8 "token10000")) fValue
                , bench "lookupCoin - existing coin"
                    $ nf (FlattenedValue.lookupCoin (encodeUtf8 "policy500") (encodeUtf8 "token999999")) fValue
                , bench "deleteCoin - not found"
                    $ nf (FlattenedValue.deleteCoin (encodeUtf8 "policy500") (encodeUtf8 "token10000")) fValue
                , bench "deleteCoin - existing coin"
                    $ nf (FlattenedValue.deleteCoin (encodeUtf8 "policy500") (encodeUtf8 "token999999")) fValue
                , bench "byPolicyId - not found"
                    $ nf (FlattenedValue.byPolicyId (encodeUtf8 "notHere")) fValue
                , bench "byPolicyId - existing policy"
                    $ nf (FlattenedValue.byPolicyId (encodeUtf8 "policy500")) fValue
                , bench "byTokenName - not found"
                    $ nf (FlattenedValue.byTokenName (encodeUtf8 "notHere")) fValue
                , bench "byTokenName - existing token"
                    $ nf (FlattenedValue.byTokenName (encodeUtf8 "token999999")) fValue
                ]
        , env setupEnvNested2 $ \ ~vals ->
            bgroup "NestedValue"
                [ bench "union - two different values"
                    $ nf (uncurry NestedValue.union) vals
                , bench "valueContains - is not sub-value"
                    $ nf (uncurry NestedValue.valueContains) vals
                ]
        , env setupEnvFlattened2 $ \ ~vals ->
            bgroup "FlattenedValue"
                [ bench "union - two different values"
                    $ nf (uncurry FlattenedValue.union) vals
                , bench "valueContains - is not sub-value"
                    $ nf (uncurry FlattenedValue.valueContains) vals
                ]
        , env setupEnvNested1andInv $ \ ~vals ->
            bgroup "NestedValue"
                [ bench "union - union with inverse"
                    $ nf (uncurry NestedValue.union) vals
                , bench "valueContains - is sub-value"
                    $ nf (uncurry NestedValue.valueContains) vals
                ]
        , env setupEnvFlattened1andInv $ \ ~vals ->
            bgroup "FlattenedValue"
                [ bench "union - union with inverse"
                    $ nf (uncurry FlattenedValue.union) vals
                , bench "valueContains - is sub-value"
                    $ nf (uncurry FlattenedValue.valueContains) vals
                ]
        ]
