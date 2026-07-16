{-# LANGUAGE TypeApplications #-}

module Array.Spec (arrayTests) where

import Control.Exception (ErrorCall)
import Data.Either (isLeft)
import PlutusCore.Test (pureTry)
import PlutusTx.Builtins.Internal qualified as BI

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (Assertion, assertBool, testCase, (@?=))
import Prelude

-- The wrapper must fail exactly where the on-chain builtin fails: any index outside
-- @[0..length)@, including one exceeding @maxBound :: Int@, is an error rather than
-- a wrap-around lookup.
arrayTests :: TestTree
arrayTests =
  testGroup
    "Array"
    [ testGroup
        "multiIndexArray"
        [ testCase "in-order with duplicates" $
            unList (BI.multiIndexArray (BI.BuiltinList [2, 0, 0, 1]) arr) @?= [30, 10, 10, 20]
        , testCase "index exceeding maxBound::Int fails" $
            throwsErrorCall (BI.multiIndexArray (BI.BuiltinList [2 ^ (64 :: Int) + 2]) arr)
        , testCase "out-of-bounds index fails even if the result is not fully demanded" $
            throwsErrorCall
              ( case unList (BI.multiIndexArray (BI.BuiltinList [0, 3]) arr) of
                  x : _ -> x
                  [] -> 0
              )
        ]
    ]
  where
    arr :: BI.BuiltinArray BI.BuiltinInteger
    arr = BI.listToArray (BI.BuiltinList [10, 20, 30])

    unList :: BI.BuiltinList a -> [a]
    unList (BI.BuiltinList xs) = xs

    throwsErrorCall :: a -> Assertion
    throwsErrorCall x =
      assertBool "expected the evaluation to fail" (isLeft (pureTry @ErrorCall x))
