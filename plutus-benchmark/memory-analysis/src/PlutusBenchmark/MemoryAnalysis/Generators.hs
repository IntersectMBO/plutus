module PlutusBenchmark.MemoryAnalysis.Generators
  ( generateUniformValue
  , generateWorstCaseValue
  , indexToKey
  ) where

import Prelude

import Data.ByteString qualified as BS
import Data.Map.Strict qualified as Map
import Data.Word (Word8)
import PlutusCore.Value (K, Value)
import PlutusCore.Value qualified as Value

{-| Generate unique key for given index (deterministic, no randomness).
Encodes index as variable-length ByteString to guarantee uniqueness.
Keys must be unique and not minimal (may need >1 byte for large indices). -}
indexToKey :: Int -> K
indexToKey idx =
  let
    -- Encode index as bytes (little-endian for simplicity)
    bytes =
      if idx < 256
        then [fromIntegral idx :: Word8]
        else
          let b0 = fromIntegral (idx `mod` 256) :: Word8
              b1 = fromIntegral ((idx `div` 256) `mod` 256) :: Word8
              b2 = fromIntegral ((idx `div` 65536) `mod` 256) :: Word8
              b3 = fromIntegral ((idx `div` 16777216) `mod` 256) :: Word8
           in filter (/= 0) [b3, b2, b1, b0] ++ [fromIntegral (idx `mod` 256) :: Word8]
    bs = BS.pack bytes
   in
    case Value.k bs of
      Just k -> k
      Nothing -> error $ "indexToKey: invalid key for index " ++ show idx

{-| Generate Value with uniform token distribution.
totalSize = numPolicies × tokensPerPolicy
Used for: real-case memory analysis, lookup benchmarks -}
generateUniformValue
  :: Int -- numPolicies
  -> Int -- tokensPerPolicy
  -> Value
generateUniformValue numPolicies tokensPerPolicy =
  let
    -- Use quantity=1 to avoid normalization removal
    qty = case Value.quantity 1 of
      Just q -> q
      Nothing -> error "generateUniformValue: invalid quantity"

    -- Generate unique policy IDs
    policyIds = [indexToKey (i * 1000) | i <- [0 .. numPolicies - 1]]

    -- For each policy, generate tokensPerPolicy unique token names
    nestedMap =
      [ ( policyId
        , Map.fromList
            [ (indexToKey (policyIdx * 1000 + tokenIdx), qty)
            | tokenIdx <- [1 .. tokensPerPolicy]
            ]
        )
      | (policyIdx, policyId) <- zip [0 ..] policyIds
      ]
   in
    Value.pack (Map.fromList nestedMap)

{-| Generate worst-case Value for memory costing (flattened structure).
Each policy has exactly 1 token (singleton inner map).
totalSize = numPolicies = numTokens
Used for: worst-case memory model derivation (ValueData costing)
Maximizes outer map overhead relative to totalSize. -}
generateWorstCaseValue
  :: Int -- totalSize (= numPolicies = numTokens)
  -> Value
generateWorstCaseValue totalSize =
  let
    -- Use quantity=1 to avoid normalization removal
    qty = case Value.quantity 1 of
      Just q -> q
      Nothing -> error "generateWorstCaseValue: invalid quantity"

    -- Each policy gets a unique ID and contains exactly one token
    -- Policy i has token (i+1000) to ensure distinct keys
    nestedMap =
      [ (indexToKey i, Map.singleton (indexToKey (i + 1000)) qty)
      | i <- [0 .. totalSize - 1]
      ]
   in
    Value.pack (Map.fromList nestedMap)
