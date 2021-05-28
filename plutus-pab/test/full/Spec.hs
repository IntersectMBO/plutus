module Main
    ( main
    ) where

import qualified Plutus.PAB.CoreSpec
import qualified Plutus.PAB.Events.ContractSpec
import           Test.Tasty                     (defaultMain, testGroup)

main :: IO ()
main =
    defaultMain $
    testGroup
        "all tests"
        [ Plutus.PAB.CoreSpec.tests
        , Plutus.PAB.Events.ContractSpec.tests
        ]
