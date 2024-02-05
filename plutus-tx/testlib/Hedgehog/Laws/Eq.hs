{-# LANGUAGE OverloadedStrings #-}

module Hedgehog.Laws.Eq where

import Hedgehog qualified
import Hedgehog.Laws.Common
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Hedgehog (testProperty)
import Prelude

eqLaws :: (Show a, Eq a) => Hedgehog.Gen a -> TestTree
eqLaws g =
  testGroup
    "equivalence relation laws"
    [ testProperty "reflexive" (prop_reflexive g (==))
    , testProperty "symmetric" (prop_symmetric g (==))
    , testProperty "transitive" (prop_transitive g (==))
    ]
