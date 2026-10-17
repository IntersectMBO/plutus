{-# LANGUAGE OverloadedStrings #-}

module Data.AssocMap.Spec (assocMapTests) where

import PlutusCore.Data (Data (B, Constr, I, List, Map))
import PlutusTx.Data.AssocMap qualified as AssocMap
import PlutusTx.IsData qualified as IsData
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (Assertion, testCase, (@?=))
import Prelude (Integer, Maybe (..), fmap, ($))

assocMapTests :: TestTree
assocMapTests =
  testGroup
    "PlutusTx.Data.AssocMap FromData tests"
    [ testCase "rejects Constr data" $ assertDecodesTo (Constr 0 []) Nothing
    , testCase "rejects List data" $ assertDecodesTo (List []) Nothing
    , testCase "rejects I data" $ assertDecodesTo (I 1) Nothing
    , testCase "rejects B data" $ assertDecodesTo (B "bytes") Nothing
    , testCase "decodes an empty map" $ assertDecodesTo (Map []) (Just [])
    , testCase "decodes a populated map" $
        assertDecodesTo (Map [(I 1, I 2), (I 3, I 4)]) (Just [(1, 2), (3, 4)])
    ]

assertDecodesTo :: Data -> Maybe [(Integer, Integer)] -> Assertion
assertDecodesTo d expected =
  fmap AssocMap.toSOPList
    (IsData.fromData d :: Maybe (AssocMap.Map Integer Integer))
    @?= expected
