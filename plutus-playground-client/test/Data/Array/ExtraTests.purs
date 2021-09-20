module Data.Array.ExtraTests
  ( all
  ) where

import Prelude
import Data.Array (length)
import Data.Array.Extra (collapse, move)
import Data.Map (Map)
import Data.Map as Map
import Data.Tuple.Nested ((/\))
import Test.QuickCheck (arbitrary, (===))
import Test.QuickCheck.Gen (Gen)
import Test.Unit (TestSuite, suite, test)
import Test.Unit.Assert (equal)
import Test.Unit.QuickCheck (quickCheck)
import TestUtils (genIndex, genLooseIndex)

all :: TestSuite
all =
  suite "Data.Array.Extra" do
    moveTests
    collapseTests

moveTests :: TestSuite
moveTests = do
  suite "move" do
    test "length is always preserved" do
      quickCheck do
        xs <- arbitrary :: Gen (Array String)
        source <- genLooseIndex xs
        destination <- genLooseIndex xs
        pure $ length xs === length (move source destination xs)
    test "identity move" do
      quickCheck do
        before <- arbitrary :: Gen (Array String)
        source <- genIndex before
        let
          after = move source source before
        pure $ before === after
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

collapseTests :: TestSuite
collapseTests = do
  suite "collapse" do
    test "Empty." do
      equal
        (collapse ([] :: Array (Map Boolean String)))
        []
    test "Concrete example." do
      equal
        ( collapse
            [ Map.fromFoldable [ "Foo" /\ true, "Bar" /\ false ]
            , Map.fromFoldable [ "Quux" /\ true, "Loop" /\ true ]
            ]
        )
        [ 0 /\ "Bar" /\ false
        , 0 /\ "Foo" /\ true
        , 1 /\ "Loop" /\ true
        , 1 /\ "Quux" /\ true
        ]
