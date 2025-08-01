{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Data.ByteString (ByteString)
import Data.List (groupBy)
import Data.Map.Strict qualified as Map
import Data.Text qualified as T
import Data.Text.Encoding (encodeUtf8)

import PlutusBenchmark.Values.FlattenedValue qualified as FlattenedValue
import PlutusBenchmark.Values.NestedValue qualified as NestedValue

import Criterion.Main (bench, bgroup, defaultMain, env, whnf)

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

setupInsertEnv :: IO (ByteString, ByteString, NestedValue.Value, FlattenedValue.Value)
setupInsertEnv = do
    let polId = encodeUtf8 "policyId"
        tokName = encodeUtf8 "tokenName"
        (nValue, fValue) = mkMockValues 100 20 (replicate 200 200)
    pure (polId, tokName, nValue, fValue)


main :: IO ()
main = defaultMain [
    env setupInsertEnv $ \ ~(polId, tokName, nValue, fValue) ->
        bgroup "insertCoin"
            [ bench "NestedValue" $ whnf (NestedValue.insertCoin polId tokName 200) nValue
            , bench "FlattenedValue" $ whnf (FlattenedValue.insertCoin polId tokName 200) fValue
            ]
  ]
