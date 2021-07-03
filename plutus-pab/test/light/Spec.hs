module Main
    ( main
    ) where

import qualified Cardano.Metadata.ServerSpec
import qualified Cardano.Metadata.TypesSpec
import qualified Cardano.Wallet.ServerSpec
import           Test.Tasty                  (defaultMain, testGroup)

main :: IO ()
main =
    defaultMain $
    testGroup
        "all tests"
        [ Cardano.Metadata.ServerSpec.tests
        , Cardano.Metadata.TypesSpec.tests
        , Cardano.Wallet.ServerSpec.tests
        ]
