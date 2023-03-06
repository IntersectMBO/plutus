module Evaluation.Builtins.BLS12_381 (test_BLS12_381)
where

import Evaluation.Builtins.BLS12_381.HaskellTests as HaskellTests
import Evaluation.Builtins.BLS12_381.PlutusTests as PlutusTests

import Test.Tasty

{-

import Text.Show.Pretty (ppShow)
  import Data.Kind (Type)
  import Test.Tasty
  import Test.Tasty.Hedgehog
  import Test.Tasty.HUnit
  import PlutusPrelude
-}


{- TODO:
    * Check the first three bits of compressed points
    * Unit tests for known values.
    * Make some testable class to reduce duplication in the tests?
      - Be careful about what would happen if we make conformance tests.
-}

test_BLS12_381 :: TestTree
test_BLS12_381 =
    testGroup "BLS12-381"
    [ HaskellTests.tests
    , PlutusTests.tests
    ]
