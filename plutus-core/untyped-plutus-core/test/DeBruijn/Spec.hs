{-# LANGUAGE TypeFamilies #-}
module DeBruijn.Spec (test_debruijn) where

import DeBruijn.FlatNatWord (test_flatNatWord)
import DeBruijn.Scope (test_scope)
import DeBruijn.UnDeBruijnify (test_undebruijnify)
import Test.Tasty
import Test.Tasty.Extras

test_debruijn :: TestTree
test_debruijn = runTestNestedIn ["untyped-plutus-core","test"] $
               testNested "DeBruijn"
                [ test_undebruijnify
                , test_scope
                , pure test_flatNatWord
                ]
