module Data.Array.ExtraTests
       ( all
       ) where

import Prelude

import Control.Monad.Eff.Random (RANDOM)
import Data.Array (length)
import Data.Array.Extra (move)
import Test.QuickCheck (arbitrary)
import Test.QuickCheck.Gen (Gen)
import Test.Unit (TestSuite, suite, test)
import Test.Unit.Assert (equal)
import Test.Unit.QuickCheck (quickCheck)
import TestUtils (genIndex, genLooseIndex)

all :: forall eff. TestSuite (random :: RANDOM | eff)
all =
  suite "Data.Array.Extra" do
    moveTests

moveTests :: forall eff. TestSuite (random :: RANDOM | eff)
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
        let after = move source source before
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
