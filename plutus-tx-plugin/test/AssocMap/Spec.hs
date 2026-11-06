{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NegativeLiterals #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -fplugin-opt Plinth.Plugin:context-level=0 #-}
{-# OPTIONS_GHC -fplugin-opt Plinth.Plugin:defer-errors #-}
-- CSE is very unstable and produces different output, likely depending on the version of either
-- @unordered-containers@ or @hashable@.
{-# OPTIONS_GHC -fplugin-opt Plinth.Plugin:max-cse-iterations=0 #-}

module AssocMap.Spec where

import PlutusTx.Builtins qualified as Builtins
import PlutusTx.Code
import PlutusTx.Data.AssocMap qualified as Data.AssocMap
import PlutusTx.IsData ()
import PlutusTx.IsData qualified as IsData
import PlutusTx.Lift (liftCodeDef)
import PlutusTx.Prelude qualified as PlutusTx
import PlutusTx.TH (compile)
import PlutusTx.Test

import AssocMap.Golden
import AssocMap.Properties1
import AssocMap.Properties2
import AssocMap.Properties3
import AssocMap.Semantics

import Test.Tasty (TestTree, localOption, testGroup)
import Test.Tasty.Extras
import Test.Tasty.Hedgehog (HedgehogTestLimit (..), testProperty)
import Test.Tasty.HUnit (Assertion, testCase, (@?=))

goldenTests :: TestNested
goldenTests =
  testNested "Budget" . pure $
    testNestedGhc
      [ goldenBundle "map1" map1 (map1 `unsafeApplyCode` liftCodeDef 100)
      , goldenBundle "map2" map2 (map2 `unsafeApplyCode` liftCodeDef 100)
      , goldenBundle "map3" map3 (map3 `unsafeApplyCode` liftCodeDef 100)
      ]

propertyTests :: TestTree
propertyTests =
  localOption (HedgehogTestLimit (Just 10)) $
    testGroup
      "Map property tests"
      [ testProperty "safeFromList" safeFromListSpec
      , testProperty "unsafeFromList" unsafeFromListSpec
      , testProperty "lookup" lookupSpec
      , testProperty "member" memberSpec
      , testProperty "insert" insertSpec
      , testProperty "all" allSpec
      , testProperty "any" anySpec
      , testProperty "keys" keysSpec
      , testProperty "elems" elemsSpec
      , testProperty "noDuplicateKeys" noDuplicateKeysSpec
      , testProperty "delete" deleteSpec
      , testProperty "union" unionSpec
      , testProperty "unionWith" unionWithSpec
      , testProperty "filter" filterSpec
      , testProperty "mapWithKey" mapWithKeySpec
      , testProperty "mapMaybe" mapMaybeSpec
      , testProperty "mapMaybeWithKey" mapMaybeWithKeySpec
      , testProperty "builtinDataEncoding" builtinDataEncodingSpec
      , fromBuiltinDataTests
      ]

fromBuiltinDataProgram ::
  CompiledCode
    ( PlutusTx.BuiltinData
      -> PlutusTx.Maybe [(PlutusTx.Integer, PlutusTx.Integer)]
    )
fromBuiltinDataProgram =
  $$( compile
        [||
        \d -> PlutusTx.fmap Data.AssocMap.toSOPList (IsData.fromBuiltinData d)
        ||]
    )

fromBuiltinDataTests :: TestTree
fromBuiltinDataTests =
  testGroup
    "Data.AssocMap FromData"
    [ testCase "rejects Constr data" $
        assertDecodesTo (Builtins.mkConstr 0 []) PlutusTx.Nothing
    , testCase "rejects List data" $
        assertDecodesTo (Builtins.mkList []) PlutusTx.Nothing
    , testCase "rejects I data" $
        assertDecodesTo (Builtins.mkI 1) PlutusTx.Nothing
    , testCase "rejects B data" $
        assertDecodesTo (Builtins.mkB "bytes") PlutusTx.Nothing
    , testCase "decodes an empty map" $
        assertDecodesTo (Builtins.mkMap []) (PlutusTx.Just [])
    , testCase "decodes a populated map" $
        assertDecodesTo
          ( Builtins.mkMap
              [ (Builtins.mkI 1, Builtins.mkI 2)
              , (Builtins.mkI 3, Builtins.mkI 4)
              ]
          )
          (PlutusTx.Just [(1, 2), (3, 4)])
    ]

assertDecodesTo ::
  PlutusTx.BuiltinData
  -> PlutusTx.Maybe [(PlutusTx.Integer, PlutusTx.Integer)]
  -> Assertion
assertDecodesTo d expected =
  evaluationResultMatchesHaskell
    (fromBuiltinDataProgram `unsafeApplyCode` liftCodeDef d)
    (@?=)
    expected
