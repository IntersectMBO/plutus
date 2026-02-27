{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_GHC -fexpose-all-unfoldings #-}
{-# OPTIONS_GHC -fno-full-laziness #-}
{-# OPTIONS_GHC -fno-ignore-interface-pragmas #-}
{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}
{-# OPTIONS_GHC -fno-spec-constr #-}
{-# OPTIONS_GHC -fno-specialise #-}
{-# OPTIONS_GHC -fno-strictness #-}
{-# OPTIONS_GHC -fno-unbox-small-strict-fields #-}
{-# OPTIONS_GHC -fno-unbox-strict-fields #-}
{-# OPTIONS_GHC -fplugin PlutusTx.Plugin #-}

module Spec.MintValue.V3 where

import PlutusTx.Prelude

import Data.Coerce (coerce)
import PlutusLedgerApi.Test.V1.Value ()
import PlutusLedgerApi.Test.V3.MintValue ()
import PlutusLedgerApi.V1.Value (AssetClass (..), Value (..), flattenValue)
import PlutusLedgerApi.V3.MintValue (MintValue (..), mintValueBurned, mintValueMinted)
import PlutusTx.AssocMap qualified as Map
import PlutusTx.Code (CompiledCode, unsafeApplyCode)
import PlutusTx.Lift (liftCodeDef)
import PlutusTx.List qualified as List
import PlutusTx.TH (compile)
import PlutusTx.Test.Run.Code (evaluationResultMatchesHaskell)
import Test.QuickCheck qualified as QC
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.QuickCheck (Property, testProperty, (===))
import Prelude qualified as Haskell

tests :: TestTree
tests = testGroup "MintValue" [testPropsInHaskell, testPropsInPlinth]

--------------------------------------------------------------------------------
-- MintValue properties --------------------------------------------------------

prop_MintValueBuiltinData :: Either Value MintValue -> Bool
prop_MintValueBuiltinData values =
  let (value, mintValue) =
        case values of
          Left v -> (v, coerce v)
          Right mv -> (coerce mv, mv)
   in toBuiltinData mintValue == toBuiltinData value

prop_AssetClassIsEitherMintedOrBurned :: MintValue -> Bool
prop_AssetClassIsEitherMintedOrBurned (mint :: MintValue) =
  let assetClasses v = [AssetClass (cs, tn) | (cs, tn, _q) <- flattenValue v]
      minted = assetClasses (mintValueMinted mint)
      burned = assetClasses (mintValueBurned mint)
   in List.all (`List.notElem` burned) minted

prop_MintValueMintedIsPositive :: MintValue -> Bool
prop_MintValueMintedIsPositive mint =
  List.all
    (List.all (> 0) . Map.elems)
    (Map.elems (getValue (mintValueMinted mint)))

prop_MintValueBurnedIsPositive :: MintValue -> Bool
prop_MintValueBurnedIsPositive mint =
  List.all
    (List.all (> 0) . Map.elems)
    (Map.elems (getValue (mintValueBurned mint)))

--------------------------------------------------------------------------------
-- Haskell-evaluated properties ------------------------------------------------

testPropsInHaskell :: TestTree
testPropsInHaskell =
  testGroup
    "Haskell"
    [ test_Hask_MintValueBuiltinData
    , test_Hask_AssetClassIsEitherMintedOrBurned
    , test_Hask_MintValueMintedIsPositive
    , test_Hask_MintValueBurnedIsPositive
    ]

test_Hask_MintValueBuiltinData :: TestTree
test_Hask_MintValueBuiltinData =
  testProperty "Builtin data representation of MintValue and Value is the same"
    $ scaleTestsBy 5 prop_MintValueBuiltinData

test_Hask_AssetClassIsEitherMintedOrBurned :: TestTree
test_Hask_AssetClassIsEitherMintedOrBurned =
  testProperty "Asset class is either minted or burned"
    $ scaleTestsBy 5 prop_AssetClassIsEitherMintedOrBurned

test_Hask_MintValueMintedIsPositive :: TestTree
test_Hask_MintValueMintedIsPositive =
  testProperty "MintValue minted is positive"
    $ scaleTestsBy 5 prop_MintValueMintedIsPositive

test_Hask_MintValueBurnedIsPositive :: TestTree
test_Hask_MintValueBurnedIsPositive =
  testProperty "MintValue burned is positive"
    $ scaleTestsBy 5 prop_MintValueBurnedIsPositive

--------------------------------------------------------------------------------
-- CEK-evaluated properties ----------------------------------------------------

testPropsInPlinth :: TestTree
testPropsInPlinth =
  testGroup
    "Plinth"
    [ test_Plinth_MintValueBuiltinData
    , test_Plinth_AssetClassIsEitherMintedOrBurned
    , test_Plinth_MintValueMintedIsPositive
    , test_Plinth_MintValueBurnedIsPositive
    ]

test_Plinth_MintValueBuiltinData :: TestTree
test_Plinth_MintValueBuiltinData =
  testProperty "Builtin data representation of MintValue and Value is the same"
    $ cekProp
    . \values ->
      $$(compile [||prop_MintValueBuiltinData||])
        `unsafeApplyCode` liftCodeDef values

test_Plinth_AssetClassIsEitherMintedOrBurned :: TestTree
test_Plinth_AssetClassIsEitherMintedOrBurned =
  testProperty "Asset class is either minted or burned"
    $ cekProp
    . \mintValue ->
      $$(compile [||prop_AssetClassIsEitherMintedOrBurned||])
        `unsafeApplyCode` liftCodeDef mintValue

test_Plinth_MintValueMintedIsPositive :: TestTree
test_Plinth_MintValueMintedIsPositive =
  testProperty "MintValue minted is positive" $ cekProp . \mintValue ->
    $$(compile [||prop_MintValueMintedIsPositive||])
      `unsafeApplyCode` liftCodeDef mintValue

test_Plinth_MintValueBurnedIsPositive :: TestTree
test_Plinth_MintValueBurnedIsPositive =
  testProperty "MintValue burned is positive" $ cekProp . \mintValue ->
    $$(compile [||prop_MintValueBurnedIsPositive||])
      `unsafeApplyCode` liftCodeDef mintValue

--------------------------------------------------------------------------------
-- Helper functions ------------------------------------------------------------

scaleTestsBy :: QC.Testable prop => Haskell.Int -> prop -> QC.Property
scaleTestsBy factor =
  QC.withMaxSuccess (100 Haskell.* factor) . QC.mapSize (Haskell.* factor)

cekProp :: CompiledCode Bool -> Property
cekProp code = evaluationResultMatchesHaskell code (===) True
