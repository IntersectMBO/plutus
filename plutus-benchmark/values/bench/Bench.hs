module Bench (main) where

import PlutusBenchmark.Values.FlattenedValue (FlattenedValue)
import PlutusBenchmark.Values.FlattenedValue qualified as FlattenedValue
import PlutusBenchmark.Values.NestedValue (NestedValue)
import PlutusBenchmark.Values.NestedValue qualified as NestedValue

import Criterion.Main

setupInsertEnv :: IO (ByteString, ByteString, NestedValue, FlattenedValue)
setupInsertEnv = do
    let polId = "policyId"
        tokName = "tokenName"
        nValue = mkMockNestedValue 1000
        fValue = mkMockFlattenedValue
    pure (polId, tokName, NestedValue.insertCoin polId tokName nValue NestedValue.empty, fValue)


main :: IO ()
main = defaultMain [
    env setupInsertEnv $ \(polId, tokName, nValue, fValue) ->
        bgroup "insertCoin"
            [ bench "NestedValue" $ whnf (NestedValue.insertCoin polId tokName nValue)
            , bench "FlattenedValue" $ whnf (FlattenedValue.insertCoin polId tokName fValue)
            ]
  ]
