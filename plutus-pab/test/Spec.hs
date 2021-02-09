module Main
    ( main
    ) where

import qualified Cardano.Metadata.ServerSpec
import qualified Cardano.Metadata.TypesSpec
import qualified Cardano.Wallet.MockSpec
import qualified Plutus.PAB.CoreSpec
import qualified Plutus.PAB.Events.ContractSpec
import qualified Plutus.PAB.RelationSpec
import           Test.Tasty                     (defaultMain, testGroup)

main :: IO ()
main =
    defaultMain $
    testGroup
        "all tests"
        [ Plutus.PAB.CoreSpec.tests
        , Plutus.PAB.RelationSpec.tests
        , Plutus.PAB.Events.ContractSpec.tests
        , Cardano.Metadata.ServerSpec.tests
        , Cardano.Metadata.TypesSpec.tests
        , Cardano.Wallet.MockSpec.tests
        ]
