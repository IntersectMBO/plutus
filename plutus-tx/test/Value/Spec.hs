{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}

module Value.Spec (valueTests) where

import Control.Exception (ErrorCall)
import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Data.Either (isLeft)
import Data.String (fromString)
import PlutusCore.Test (pureTry)
import PlutusCore.Value (Value)
import PlutusCore.Value qualified as Value
import PlutusTx.Builtins.Internal qualified as BI

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (Assertion, assertBool, testCase, (@?=))
import Prelude

-- The Haskell implementations of the CIP-0168 builtins must agree with the on-chain
-- builtins: `keepPolicies` and `dropPolicies` accept a list of exactly
-- 'Value.policyFilterMaxIds' ids and fail on a longer one, repeated ids and ids longer than
-- a policy id included.
valueTests :: TestTree
valueTests =
  testGroup
    "Value"
    [ testCase "policies are ascending, lovelace included" $
        policies mixed @?= ["", "aaa", "bbb"]
    , testCase "assetCount counts (currency, token) pairs" $
        BI.assetCount mixed @?= 5
    , testGroup
        "keepPolicies"
        [ testCase "keeps the listed policies with their tokens" $
            unValue (BI.keepPolicies (ids ["bbb", "absent"]) mixed)
              @?= fromTriples [("bbb", "t1", 1), ("bbb", "t2", 3)]
        , testCase "accepts a list at the id bound" $
            unValue (BI.keepPolicies (absentIds Value.policyFilterMaxIds) mixed) @?= Value.empty
        , testCase "fails on a list above the id bound" $
            throwsErrorCall (BI.keepPolicies (absentIds (Value.policyFilterMaxIds + 1)) mixed)
        , testCase "repeated ids count toward the bound" $ do
            unValue (BI.keepPolicies (atBound "aaa") mixed)
              @?= fromTriples [("aaa", "t1", 2), ("aaa", "t2", -7)]
            throwsErrorCall (BI.keepPolicies (overBound "aaa") mixed)
        , testCase "over-long ids count toward the bound" $ do
            unValue (BI.keepPolicies (atBound overLong) mixed) @?= Value.empty
            throwsErrorCall (BI.keepPolicies (overBound overLong) mixed)
        ]
    , testGroup
        "dropPolicies"
        [ testCase "drops the listed policies with their tokens" $
            unValue (BI.dropPolicies (ids ["", "aaa", "absent"]) mixed)
              @?= fromTriples [("bbb", "t1", 1), ("bbb", "t2", 3)]
        , testCase "accepts a list at the id bound" $
            unValue (BI.dropPolicies (absentIds Value.policyFilterMaxIds) mixed) @?= unValue mixed
        , testCase "fails on a list above the id bound" $
            throwsErrorCall (BI.dropPolicies (absentIds (Value.policyFilterMaxIds + 1)) mixed)
        , testCase "repeated ids count toward the bound" $ do
            unValue (BI.dropPolicies (atBound "aaa") mixed)
              @?= fromTriples [("", "", 2000000), ("bbb", "t1", 1), ("bbb", "t2", 3)]
            throwsErrorCall (BI.dropPolicies (overBound "aaa") mixed)
        , testCase "over-long ids count toward the bound" $ do
            unValue (BI.dropPolicies (atBound overLong) mixed) @?= unValue mixed
            throwsErrorCall (BI.dropPolicies (overBound overLong) mixed)
        ]
    , testCase "keepPolicies and dropPolicies partition the Value" $
        let ps = ids ["", "bbb"]
         in unValue (BI.unionValue (BI.keepPolicies ps mixed) (BI.dropPolicies ps mixed))
              @?= unValue mixed
    ]
  where
    mixed :: BI.BuiltinValue
    mixed =
      BI.BuiltinValue $
        fromTriples
          [ ("bbb", "t1", 1)
          , ("", "", 2000000)
          , ("aaa", "t1", 2)
          , ("bbb", "t2", 3)
          , ("aaa", "t2", -7)
          ]

    policies :: BI.BuiltinValue -> [ByteString]
    policies v = case BI.policies v of BI.BuiltinList xs -> [b | BI.BuiltinByteString b <- xs]

    unValue :: BI.BuiltinValue -> Value
    unValue (BI.BuiltinValue v) = v

    ids :: [ByteString] -> BI.BuiltinList BI.BuiltinByteString
    ids = BI.BuiltinList . map BI.BuiltinByteString

    absentIds :: Int -> BI.BuiltinList BI.BuiltinByteString
    absentIds n = ids [fromString ("absent" <> show i) | i <- [1 .. n]]

    atBound, overBound :: ByteString -> BI.BuiltinList BI.BuiltinByteString
    atBound = ids . replicate Value.policyFilterMaxIds
    overBound = ids . replicate (Value.policyFilterMaxIds + 1)

    overLong :: ByteString
    overLong = BS.replicate (Value.maxKeyLen + 1) 0

    throwsErrorCall :: a -> Assertion
    throwsErrorCall x =
      assertBool "expected the evaluation to fail" (isLeft (pureTry @ErrorCall x))

-- | Build a `Value` from @(currency, token, quantity)@ triples with the off-chain `insertCoin`.
fromTriples :: [(ByteString, ByteString, Integer)] -> Value
fromTriples = go (BI.BuiltinValue Value.empty)
  where
    go (BI.BuiltinValue v) [] = v
    go acc ((c, t, q) : rest) =
      go (BI.insertCoin (BI.BuiltinByteString c) (BI.BuiltinByteString t) q acc) rest
