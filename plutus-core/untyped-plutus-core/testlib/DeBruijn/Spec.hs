module DeBruijn.Spec (test_debruijn) where

import DeBruijn.FlatNatWord (test_flatNatWord)
import DeBruijn.Scope (test_scope)
import DeBruijn.UnDeBruijnify (test_undebruijnify)
import Test.Tasty
import Test.Tasty.Extras

test_debruijn :: TestTree
test_debruijn =
  runTestNested ["untyped-plutus-core", "test", "DeBruijn"] $
    [ test_undebruijnify
    , test_scope
    , test_flatNatWord
    ]
