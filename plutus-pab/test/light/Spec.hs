module Main
    ( main
    ) where

import qualified Cardano.Api.NetworkId.ExtraSpec
import qualified Cardano.Wallet.ServerSpec
import qualified Control.Concurrent.STM.ExtrasSpec
import           Test.Tasty                        (defaultMain, testGroup)

main :: IO ()
main =
    defaultMain $
    testGroup
        "all tests"
        [ Cardano.Api.NetworkId.ExtraSpec.tests
        , Cardano.Wallet.ServerSpec.tests
        , Control.Concurrent.STM.ExtrasSpec.tests
        ]
