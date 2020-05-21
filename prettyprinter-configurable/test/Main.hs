module Main where

import           Default
import           NonDefault

import           Test.Tasty

main :: IO ()
main = defaultMain $ testGroup "all"
    [ test_default
    , test_nonDefault
    ]
