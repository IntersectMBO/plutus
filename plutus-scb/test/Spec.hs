module Main
    ( main
    ) where

import qualified Plutus.SCB.CoreSpec
import qualified Plutus.SCB.RelationSpec
import           Test.Tasty              (defaultMain, testGroup)

main :: IO ()
main =
    defaultMain $
    testGroup
        "all tests"
        [ Plutus.SCB.CoreSpec.tests
        , Plutus.SCB.RelationSpec.tests
        ]
