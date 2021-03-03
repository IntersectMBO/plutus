module Main
    ( main
    ) where

import qualified Cardano.Metadata.ServerSpec
import qualified Cardano.Metadata.TypesSpec
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
        , Cardano.Metadata.ServerSpec.tests
        , Cardano.Metadata.TypesSpec.tests
        ]
