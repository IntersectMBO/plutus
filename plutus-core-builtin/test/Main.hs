-- | Dynamic built-ins tests.

{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE OverloadedStrings #-}

module Main
    ( main
    ) where

import           Factorial  (test_dynamicFactorial)
import           String     (test_dynamicStrings)

import           Test.Tasty

test_dynamicBuiltins :: TestTree
test_dynamicBuiltins =
    testGroup "Dynamic built-ins"
        [ test_dynamicFactorial
        , test_dynamicStrings
        ]

main :: IO ()
main = defaultMain test_dynamicBuiltins
