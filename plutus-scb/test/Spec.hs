module Main
    ( main
    ) where

import qualified Cardano.Metadata.TypesSpec
import qualified Plutus.SCB.CoreSpec
import qualified Plutus.SCB.Events.ContractSpec
import qualified Plutus.SCB.RelationSpec
import           Test.Tasty                     (defaultMain, testGroup)

main :: IO ()
main =
    defaultMain $
    testGroup
        "all tests"
        [ Plutus.SCB.CoreSpec.tests
        , Plutus.SCB.RelationSpec.tests
        , Plutus.SCB.Events.ContractSpec.tests
        , Cardano.Metadata.TypesSpec.tests
        ]
