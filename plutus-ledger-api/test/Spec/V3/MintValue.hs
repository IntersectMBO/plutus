{-# LANGUAGE BlockArguments #-}

module Spec.V3.MintValue where

import Data.Set (Set)
import Data.Set qualified as Set
import PlutusLedgerApi.Test.V1.Value ()
import PlutusLedgerApi.Test.V3.MintValue ()
import PlutusLedgerApi.V1.Value (AssetClass (..), Value (..), flattenValue)
import PlutusLedgerApi.V3.MintValue (MintValue, mintValueBurned, mintValueMinted)
import PlutusTx.AssocMap qualified as Map
import PlutusTx.IsData.Class (toBuiltinData)
import Spec.V1.Data.Value (scaleTestsBy)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.QuickCheck (testProperty, (===))
import Unsafe.Coerce (unsafeCoerce)

tests :: TestTree
tests =
  testGroup
    "MintValue"
    [ test_MintValueBuiltinData
    , test_AssetClassIsEitherMintedOrBurned
    , test_MintValueMintedIsPositive
    , test_MintValueBurnedIsPositive
    ]

test_MintValueBuiltinData :: TestTree
test_MintValueBuiltinData =
  testProperty "Builtin data representation of MintValue and Value is the same" $
    scaleTestsBy 5 \(values :: Either Value MintValue) -> do
      let (value, mintValue) =
            case values of
              Left v   -> (v, unsafeCoerce v)
              Right mv -> (unsafeCoerce mv, mv)
      toBuiltinData mintValue === toBuiltinData value

test_AssetClassIsEitherMintedOrBurned :: TestTree
test_AssetClassIsEitherMintedOrBurned =
  testProperty "Asset class is either minted or burned" $
    scaleTestsBy 5 \(mintValue :: MintValue) ->
      Set.null $
        Set.intersection
          (valueAssetClasses (mintValueMinted mintValue))
          (valueAssetClasses (mintValueBurned mintValue))
  where
    valueAssetClasses :: Value -> Set AssetClass
    valueAssetClasses value =
      Set.fromList [AssetClass (cs, tn) | (cs, tn, _q) <- flattenValue value]

test_MintValueMintedIsPositive :: TestTree
test_MintValueMintedIsPositive =
  testProperty "MintValue minted is positive" $
    scaleTestsBy 5 \(mintValue :: MintValue) ->
      let Value minted = mintValueMinted mintValue
       in all (all (> 0) . Map.elems) (Map.elems minted)

test_MintValueBurnedIsPositive :: TestTree
test_MintValueBurnedIsPositive =
  testProperty "MintValue burned is positive" $
    scaleTestsBy 5 \(mintValue :: MintValue) ->
      let Value burned = mintValueBurned mintValue
       in all (all (> 0) . Map.elems) (Map.elems burned)
