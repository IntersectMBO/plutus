module Main (main) where

import V3.Spec qualified as V3

import Test.Tasty

main :: IO ()
main = defaultMain V3.allTests
