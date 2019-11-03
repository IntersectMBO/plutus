module Main
    ( main
    ) where

import qualified IOTSSpec
import           Test.Tasty (defaultMain, testGroup)

main :: IO ()
main = defaultMain $ testGroup "all tests" [IOTSSpec.tests]
