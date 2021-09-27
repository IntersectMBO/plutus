module Main
    ( main
    ) where

import qualified Plutus.PAB.CliSpec
import           Test.Tasty         (defaultMain, testGroup)

main :: IO ()
main =
    defaultMain $
    testGroup
        "all tests"
        [ Plutus.PAB.CliSpec.tests
        ]
