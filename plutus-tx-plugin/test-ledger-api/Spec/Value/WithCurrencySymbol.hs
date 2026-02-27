{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_GHC -Wno-orphans #-}
{-# OPTIONS_GHC -fno-full-laziness #-}
{-# OPTIONS_GHC -fno-ignore-interface-pragmas #-}
{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}
{-# OPTIONS_GHC -fno-spec-constr #-}
{-# OPTIONS_GHC -fno-specialise #-}
{-# OPTIONS_GHC -fno-strictness #-}
{-# OPTIONS_GHC -fno-unbox-small-strict-fields #-}
{-# OPTIONS_GHC -fno-unbox-strict-fields #-}
{-# OPTIONS_GHC -fplugin PlutusTx.Plugin #-}

module Spec.Value.WithCurrencySymbol where

import PlutusTx.Prelude

import Data.ByteString (ByteString)
import PlutusCore.Generators.QuickCheck.Builtin (ArbitraryBuiltin (arbitraryBuiltin), shrinkBuiltin)
import PlutusLedgerApi.Test.V1.Value ()
import PlutusLedgerApi.Test.V3.MintValue ()
import PlutusLedgerApi.V1.Value
  ( CurrencySymbol (..)
  , TokenName (..)
  , Value (..)
  , currencySymbol
  , singleton
  , symbols
  , tokenName
  , unCurrencySymbol
  , withCurrencySymbol
  )
import PlutusTx.AssocMap qualified as Map
import PlutusTx.Code (CompiledCode, unsafeApplyCode)
import PlutusTx.Lift (liftCodeDef)
import PlutusTx.List qualified as List
import PlutusTx.TH (compile)
import PlutusTx.Test.Run.Code (evaluationResultMatchesHaskell)
import Test.QuickCheck
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.QuickCheck (testProperty)
import Prelude qualified as Haskell

tests :: TestTree
tests = testGroup "withCurrencySymbol" [testPropsInHaskell, testPropsInPlinth]

--------------------------------------------------------------------------------
-- Properties ------------------------------------------------------------------

prop_EachCurrencySymbolGetsContinuationApplied :: Value -> Bool
prop_EachCurrencySymbolGetsContinuationApplied v =
  List.all (\cs -> withCurrencySymbol cs v False (const True)) (symbols v)

prop_CorrectTokenQuantitiesAreSelected
  :: (CurrencySymbol, TokenName, Integer) -> Bool
prop_CorrectTokenQuantitiesAreSelected (cs, tn, q) =
  [(tn, q)] == withCurrencySymbol cs (singleton cs tn q) [] Map.toList

--------------------------------------------------------------------------------
-- Test properties in Haskell --------------------------------------------------

testPropsInHaskell :: TestTree
testPropsInHaskell =
  testGroup
    "Haskell"
    [ test_Hask_EachCurrencySymbolGetsItsContinuationApplied
    , test_Hask_CorrectTokenQuantitiesAreSelected
    ]

test_Hask_EachCurrencySymbolGetsItsContinuationApplied :: TestTree
test_Hask_EachCurrencySymbolGetsItsContinuationApplied =
  testProperty "Each currency symbol in a Value gets its continuation applied"
    $ scaleTestsBy 5 prop_EachCurrencySymbolGetsContinuationApplied

test_Hask_CorrectTokenQuantitiesAreSelected :: TestTree
test_Hask_CorrectTokenQuantitiesAreSelected =
  testProperty "Correct token quantities are selected"
    $ scaleTestsBy 5 prop_CorrectTokenQuantitiesAreSelected

--------------------------------------------------------------------------------
-- Test properties in Plinth ---------------------------------------------------

testPropsInPlinth :: TestTree
testPropsInPlinth =
  testGroup
    "Plinth"
    [ test_Plinth_EachCurrencySymbolGetsItsContinuationApplied
    , test_Plinth_CorrectTokenQuantitiesAreSelected
    ]

test_Plinth_EachCurrencySymbolGetsItsContinuationApplied :: TestTree
test_Plinth_EachCurrencySymbolGetsItsContinuationApplied =
  testProperty "Each currency symbol in a Value gets its continuation applied"
    $ cekProp
    . \value ->
      $$(compile [||prop_EachCurrencySymbolGetsContinuationApplied||])
        `unsafeApplyCode` liftCodeDef value

test_Plinth_CorrectTokenQuantitiesAreSelected :: TestTree
test_Plinth_CorrectTokenQuantitiesAreSelected =
  testProperty "Correct token quantities are selected"
    $ cekProp
    . \values ->
      $$(compile [||prop_CorrectTokenQuantitiesAreSelected||])
        `unsafeApplyCode` liftCodeDef values

--------------------------------------------------------------------------------
-- Helper functions ------------------------------------------------------------

scaleTestsBy :: Testable prop => Haskell.Int -> prop -> Property
scaleTestsBy factor =
  withMaxSuccess (100 Haskell.* factor) . mapSize (Haskell.* factor)

cekProp :: CompiledCode Bool -> Property
cekProp code = evaluationResultMatchesHaskell code (===) True

instance Arbitrary CurrencySymbol where
  arbitrary = Haskell.fmap currencySymbol (arbitraryBuiltin @ByteString)
  shrink =
    Haskell.fmap currencySymbol
      . shrinkBuiltin
      . fromBuiltin
      . unCurrencySymbol

instance Arbitrary TokenName where
  arbitrary = Haskell.fmap tokenName (arbitraryBuiltin @ByteString)
  shrink =
    Haskell.fmap tokenName
      . shrinkBuiltin
      . fromBuiltin
      . unTokenName
