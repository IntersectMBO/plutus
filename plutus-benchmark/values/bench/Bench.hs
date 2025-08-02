{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Data.List (groupBy)
import Data.Map.Strict qualified as Map
import Data.Text qualified as T
import Data.Text.Encoding (encodeUtf8)

import PlutusBenchmark.Common (getConfig)
import PlutusBenchmark.Values.FlattenedValue qualified as FlattenedValue
import PlutusBenchmark.Values.NestedValue qualified as NestedValue

import Criterion.Main (bench, bgroup, defaultMainWith, env, nf)

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

setupInsertEnvNested :: IO NestedValue.Value -- (ByteString, ByteString, NestedValue.Value)
setupInsertEnvNested = do
    let polId = BS.empty -- encodeUtf8 "policyId"
        tokName = BS.empty -- encodeUtf8 "tokenName"
        (nValue, _) = mkMockValues 10000 2000 (replicate 2000000 200)
    -- pure (polId, tokName, nValue)
    pure nValue

setupInsertEnvFlattened :: IO FlattenedValue.Value -- (ByteString, ByteString, FlattenedValue.Value)
setupInsertEnvFlattened = do
    let polId = BS.empty -- encodeUtf8 "policyId"
        tokName = BS.empty -- encodeUtf8 "tokenName"
        (_, fValue) = mkMockValues 10000 2000 (replicate 2000000 200)
    -- pure (polId, tokName, fValue)
    pure fValue


main :: IO ()
main = do
    config <- getConfig 5
    defaultMainWith config $
        [ env setupInsertEnvNested $ \ ~nValue ->
            bgroup "NestedValue"
                [ bench "insertCoin"
                    $ nf (NestedValue.insertCoin (encodeUtf8 "policy500") (encodeUtf8 "token10000") 200) nValue
                , bench "lookupCoin"
                    $ nf (NestedValue.lookupCoin (encodeUtf8 "policy500") (encodeUtf8 "token10000")) nValue
                ]
        , env setupInsertEnvFlattened $ \ ~fValue ->
            bgroup "FlattenedValue"
                [ bench "insertCoin"
                    $ nf (FlattenedValue.insertCoin (encodeUtf8 "policy500") (encodeUtf8 "token10000") 200) fValue
                , bench "lookupCoin"
                    $ nf (FlattenedValue.lookupCoin (encodeUtf8 "policy500") (encodeUtf8 "token10000")) fValue
                ]
        ]
