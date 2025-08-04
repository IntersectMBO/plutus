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

mockNumPolicies :: Int
mockNumPolicies = 10000

mockNumTokensPerPolicy :: Int
mockNumTokensPerPolicy = 2000

mockNumTokens :: Int
mockNumTokens = mockNumPolicies * mockNumTokensPerPolicy

mockTokenValues :: [Integer]
mockTokenValues = replicate mockNumTokens 200

setupInsertEnvNested :: IO NestedValue.Value
setupInsertEnvNested =
    let (nValue, _) =
            mkMockValues
                mockNumPolicies
                mockNumTokensPerPolicy
                mockTokenValues
     in pure nValue

setupInsertEnvFlattened :: IO FlattenedValue.Value
setupInsertEnvFlattened =
    let (_, fValue) =
            mkMockValues
                mockNumPolicies
                mockNumTokensPerPolicy
                mockTokenValues
     in pure fValue

main :: IO ()
main = do
    config <- getConfig 5
    defaultMainWith config $
        [ env setupInsertEnvNested $ \ ~nValue ->
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
                ]
        , env setupInsertEnvFlattened $ \ ~fValue ->
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
                ]
        ]
