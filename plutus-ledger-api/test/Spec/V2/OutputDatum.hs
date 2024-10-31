module Spec.V2.OutputDatum where

import PlutusLedgerApi.Test.V2.OutputDatum ()
import Test.Tasty
import Test.Tasty.QuickCheck

-- Define a test case for Arbitrary instance
arbitraryTest :: TestTree
arbitraryTest = testProperty "Arbitrary instance exists" $ \(_) ->
  let _ = arbitrary :: Gen OutputDatum
  in True

-- Define the main test suite
testOutputDatum :: TestTree
testOutputDatum = testGroup "OutputDatum"
  [arbitraryTest
  ]
