-- | Dynamic built-ins tests.

{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE OverloadedStrings #-}

module DynamicBuiltins.Spec
    ( test_dynamicBuiltins
    ) where

import           DynamicBuiltins.Factorial

import           Test.Tasty

test_dynamicBuiltins :: TestTree
test_dynamicBuiltins =
    testGroup "Dynamic built-ins"
        [ test_dynamicFactorial
        ]
