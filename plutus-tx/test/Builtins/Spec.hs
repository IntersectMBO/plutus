{-# LANGUAGE TypeApplications #-}

module Builtins.Spec (builtinsTests) where

import Control.Exception (ErrorCall)
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
    ]
  where
    arr :: BI.BuiltinArray BI.BuiltinInteger
    arr = BI.listToArray (BI.BuiltinList [10, 20, 30])

    throwsErrorCall :: a -> Assertion
    throwsErrorCall x =
      assertBool "expected the evaluation to fail" (isLeft (pureTry @ErrorCall x))
