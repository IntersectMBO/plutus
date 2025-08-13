{-# LANGUAGE BangPatterns      #-}
{-# LANGUAGE OverloadedStrings #-}

module PlutusBenchmark.Values.MockValues where

import Data.ByteString (ByteString)
import Data.List (groupBy)
import Data.Map.Strict qualified as Map
import Data.Monoid (Sum (..))
import Data.MonoidMap qualified as MM
import Data.Text qualified as T
import Data.Text.Encoding (encodeUtf8)

import PlutusBenchmark.Values.FlattenedValue qualified as FlattenedValue
import PlutusBenchmark.Values.MMValue qualified as MMValue
import PlutusBenchmark.Values.NestedValue qualified as NestedValue


fVal1, fVal2 :: FlattenedValue.Value
nVal1, nVal2 :: NestedValue.Value
mVal1, mVal2 :: MMValue.Value
(!nVal1, !fVal1, !mVal1) =
    mkMockValues
        mockNumPolicies1
        mockNumTokensPerPolicy1
        mockTokenValues1
(!nVal2, !fVal2, !mVal2) =
    mkMockValues
        mockNumPolicies2
        mockNumTokensPerPolicy2
        mockTokenValues2

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

polId500, tokN999999, tokN10000, polIdNotHere :: ByteString
polId500 = encodeUtf8 "policy500"
tokN999999 = encodeUtf8 "token999999"
tokN10000 = encodeUtf8 "token10000"
polIdNotHere = encodeUtf8 "notHere"

mkMockValues :: Int -> Int -> [Integer] -> (NestedValue.Value, FlattenedValue.Value, MMValue.Value)
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
        rawMMValue =
            let x = groupBy (\((p1, _), _) ((p2, _), _) -> p1 == p2) rawFlatValue
             in [ (p, tkMap) | l <- x, let p = (fst . fst) (head l), let tkMap = MM.fromList $ map (\((_, tk), am) -> (tk, Sum am)) l ]
        nestedValue = NestedValue.Value $ Map.fromList rawNestValue
        mmValue = MMValue.Value $ MM.fromList rawMMValue
     in (nestedValue, flattenedValue, mmValue)
