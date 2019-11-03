module Data.Array.ExtraTests
  ( all
  ) where

import Prelude
import Data.Array (length, null)
import Data.Array.Extra (move, intersperse)
import Test.QuickCheck (arbitrary)
import Test.QuickCheck.Gen (Gen, suchThat)
import Test.Unit (TestSuite, suite, test)
import Test.Unit.Assert (equal)
import Test.Unit.QuickCheck (quickCheck)
import TestUtils (genIndex, genLooseIndex)

all :: TestSuite
all =
  suite "Data.Array.Extra" do
    moveTests
    intersperseTests

moveTests :: TestSuite
moveTests = do
  suite "move" do
    test "length is always preserved" do
      quickCheck do
        xs <- arbitrary :: Gen (Array String)
        source <- genLooseIndex xs
        destination <- genLooseIndex xs
        pure $ length xs == length (move source destination xs)
    test "identity move" do
      quickCheck do
        before <- arbitrary :: Gen (Array String)
        source <- genIndex before
        let
          after = move source source before
        pure $ before == after
    test "Concrete example - source to left of destination" do
      equal
        [ 1, 0, 2, 3, 4 ]
        (move 0 1 [ 0, 1, 2, 3, 4 ])
    test "Concrete example - source to right of destination" do
      equal
        [ 1, 0, 2, 3, 4 ]
        (move 1 0 [ 0, 1, 2, 3, 4 ])
    test "Concrete example - source less than destination" do
      equal
        [ 0, 2, 3, 1, 4 ]
        (move 1 3 [ 0, 1, 2, 3, 4 ])
    test "Concrete example - source more than destination" do
      equal
        [ 0, 3, 1, 2, 4 ]
        (move 3 1 [ 0, 1, 2, 3, 4 ])

intersperseTests :: TestSuite
intersperseTests = do
  suite "intersperse" do
    test "Empty arrays are unchanged" do
      quickCheck do
        sep <- arbitrary :: Gen String
        pure $ intersperse sep [] == []
    test "Singleton arrays are unchanged" do
      quickCheck do
        sep <- arbitrary :: Gen String
        x <- arbitrary
        pure $ intersperse sep [ x ] == [ x ]
    test "Non-empty arrays increase their length by (2n - 1)" do
      quickCheck do
        sep <- arbitrary :: Gen String
        xs <- arbitrary `suchThat` (not <<< null)
        pure $ length (intersperse sep xs) == (2 * length xs) - 1
    test "Simple concrete example" do
      equal
        [ 1, 0, 2, 0, 3 ]
        (intersperse 0 [ 1, 2, 3 ])
