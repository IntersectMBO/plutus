{-# LANGUAGE OverloadedStrings #-}

module Hedgehog.Laws.Ord where

import Hedgehog qualified
import Hedgehog.Laws.Common
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Hedgehog (testProperty)
import Prelude

-- There is no typeclass for this, sadly
partialOrderLaws :: (Show a, Eq a) => Hedgehog.Gen a -> (a -> a -> Bool) -> TestTree
partialOrderLaws g op =
  testGroup
    "partial ordering laws"
    [ testProperty "reflexive" (prop_reflexive g op)
    , testProperty "transitive" (prop_transitive g op)
    , testProperty "antisymmetric" (prop_antisymmetric g op)
    ]

ordLaws :: (Show a, Ord a) => Hedgehog.Gen a -> TestTree
ordLaws g =
  testGroup
    "total ordering laws"
    [ partialOrderLaws g (<=)
    , testProperty "total" (prop_total g (<=))
    ]
