{-# LANGUAGE TypeApplications #-}

module Builtins.Spec (builtinsTests) where

import Control.Exception (ErrorCall)
import Data.ByteString.Char8 qualified as C8
import Data.Either (isLeft)
import PlutusCore.Test (pureTry)
import PlutusTx.Builtins.Internal qualified as BI

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (Assertion, assertBool, testCase, (@?=))
import Prelude

-- The wrappers must fail exactly where the on-chain builtins fail: arguments outside the
-- builtin's domain, including integers that do not fit in a machine 'Int', are errors rather
-- than wrap-around conversions.
builtinsTests :: TestTree
builtinsTests =
  testGroup
    "Builtins"
    [ testGroup
        "indexArray"
        [ testCase "in-range index" $ BI.indexArray arr 2 @?= 30
        , testCase "negative index fails" $ throwsErrorCall (BI.indexArray arr (-1))
        , testCase "index equal to length fails" $ throwsErrorCall (BI.indexArray arr 3)
        , testCase "index exceeding maxBound::Int fails" $
            throwsErrorCall (BI.indexArray arr (2 ^ (64 :: Int) + 2))
        ]
    , testGroup
        "indexByteString"
        [ testCase "in-range index" $ BI.indexByteString abc 2 @?= 99
        , testCase "index equal to length fails" $ throwsErrorCall (BI.indexByteString abc 3)
        , testCase "negative index fails" $ throwsErrorCall (BI.indexByteString abc (-1))
        , testCase "index exceeding maxBound::Int fails" $
            throwsErrorCall (BI.indexByteString abc (2 ^ (64 :: Int) + 2))
        ]
    , testGroup
        "sliceByteString"
        [ testCase "in-range slice" $ unBS (BI.sliceByteString 1 2 abc) @?= C8.pack "bc"
        , testCase "negative start clamps" $ unBS (BI.sliceByteString (-5) 2 abc) @?= C8.pack "ab"
        , testCase "overlong length clamps" $ unBS (BI.sliceByteString 1 100 abc) @?= C8.pack "bc"
        , testCase "start exceeding maxBound::Int fails" $
            throwsErrorCall (BI.sliceByteString (2 ^ (64 :: Int)) 2 abc)
        , testCase "length exceeding maxBound::Int fails" $
            throwsErrorCall (BI.sliceByteString 0 (2 ^ (64 :: Int)) abc)
        ]
    , testGroup
        "readBit"
        [ testCase "in-range bit index" $ BI.readBit abc 0 @?= True
        , testCase "bit index equal to bit length fails" $ throwsErrorCall (BI.readBit abc 24)
        , testCase "negative bit index fails" $ throwsErrorCall (BI.readBit abc (-1))
        , testCase "bit index exceeding maxBound::Int fails" $
            throwsErrorCall (BI.readBit abc (2 ^ (64 :: Int)))
        ]
    , testGroup
        "replicateByte"
        [ testCase "in-range byte" $ unBS (BI.replicateByte 3 65) @?= C8.pack "AAA"
        , testCase "byte above 255 fails" $ throwsErrorCall (BI.replicateByte 3 256)
        , testCase "negative byte fails" $ throwsErrorCall (BI.replicateByte 3 (-1))
        , testCase "negative count fails" $ throwsErrorCall (BI.replicateByte (-1) 65)
        ]
    , testGroup
        "caseInteger"
        [ testCase "in-range scrutinee" $ BI.caseInteger 1 [10 :: Integer, 20, 30] @?= 20
        , testCase "scrutinee equal to branch count fails" $
            throwsErrorCall (BI.caseInteger 3 [10 :: Integer, 20, 30])
        , testCase "negative scrutinee fails" $
            throwsErrorCall (BI.caseInteger (-1) [10 :: Integer, 20, 30])
        , testCase "scrutinee exceeding maxBound::Int fails" $
            throwsErrorCall (BI.caseInteger (2 ^ (64 :: Int) + 1) [10 :: Integer, 20, 30])
        ]
    ]
  where
    arr :: BI.BuiltinArray BI.BuiltinInteger
    arr = BI.listToArray (BI.BuiltinList [10, 20, 30])

    abc :: BI.BuiltinByteString
    abc = BI.BuiltinByteString (C8.pack "abc")

    unBS :: BI.BuiltinByteString -> C8.ByteString
    unBS (BI.BuiltinByteString bs) = bs

    throwsErrorCall :: a -> Assertion
    throwsErrorCall x =
      assertBool "expected the evaluation to fail" (isLeft (pureTry @ErrorCall x))
