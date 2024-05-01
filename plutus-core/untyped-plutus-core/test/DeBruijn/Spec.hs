{-# LANGUAGE TypeFamilies #-}
module DeBruijn.Spec (test_debruijn) where

import DeBruijn.FlatNatWord (test_flatNatWord)
import DeBruijn.Scope (test_scope)
import DeBruijn.UnDeBruijnify (test_undebruijnify)
import Test.Tasty
import Test.Tasty.Extras

test_debruijn :: TestTree
test_debruijn = runTestNestedM ["untyped-plutus-core", "test", "DeBruijn"] $ do
  test_undebruijnify
  test_scope
  test_flatNatWord
