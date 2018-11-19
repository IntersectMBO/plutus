-- | Dynamic built-ins tests.

{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE OverloadedStrings #-}

module DynamicBuiltins.Spec
    ( test_dynamicBuiltins
    ) where

import           DynamicBuiltins.Char      (test_collectChars)
import           DynamicBuiltins.Factorial (test_dynamicFactorial)

import           Test.Tasty

test_dynamicBuiltins :: TestTree
test_dynamicBuiltins =
    testGroup "Dynamic built-ins"
        [ test_dynamicFactorial
        , test_collectChars
        ]
