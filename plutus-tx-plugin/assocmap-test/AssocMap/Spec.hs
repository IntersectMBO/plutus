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
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:context-level=0 #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:datatypes=BuiltinCasing #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:defer-errors #-}
-- CSE is very unstable and produces different output, likely depending on the version of either
-- @unordered-containers@ or @hashable@.
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:max-cse-iterations=0 #-}

module AssocMap.Spec where

import PlutusTx.Code
import PlutusTx.IsData ()
import PlutusTx.Lift (liftCodeDef)
import PlutusTx.Test

import AssocMap.Golden
import AssocMap.Properties1
import AssocMap.Properties2
import AssocMap.Properties3
import AssocMap.Semantics

import Test.Tasty (TestTree, localOption, testGroup)
import Test.Tasty.Extras
import Test.Tasty.Hedgehog (HedgehogTestLimit (..), testProperty)

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
  localOption (HedgehogTestLimit (Just 30)) $
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
      ]
