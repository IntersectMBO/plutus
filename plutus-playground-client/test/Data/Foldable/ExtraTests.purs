module Data.Foldable.ExtraTests
  ( all
  ) where

import Prelude
import Data.Foldable (length, null)
import Data.Foldable.Extra (interleave)
import Test.QuickCheck (arbitrary)
import Test.QuickCheck.Gen (Gen, suchThat)
import Test.Unit (TestSuite, suite, test)
import Test.Unit.Assert (equal)
import Test.Unit.QuickCheck (quickCheck)

all :: TestSuite
all =
  suite "Data.Foldable.Extra" do
    interleaveTests

interleaveTests :: TestSuite
interleaveTests = do
  suite "interleave" do
    test "Empty arrays are unchanged" do
      quickCheck do
        sep <- arbitrary :: Gen String
        pure $ interleave sep [] == []
    test "Singleton arrays are unchanged" do
      quickCheck do
        sep <- arbitrary :: Gen String
        x <- arbitrary
        pure $ interleave sep [ x ] == [ x ]
    test "Non-empty arrays increase their length by (2n - 1)" do
      quickCheck do
        sep <- arbitrary :: Gen String
        xs :: Array String <- arbitrary `suchThat` (not <<< null)
        pure $ length (interleave sep xs) == (2 * length xs) - 1
    test "Simple concrete example" do
      equal
        [ 1, 0, 2, 0, 3 ]
        (interleave 0 [ 1, 2, 3 ])
