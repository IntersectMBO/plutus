{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE TypeApplications #-}
module Spec.PingPong(tests) where

import           Language.Plutus.Contract
import           Language.Plutus.Contract.Test

import           Language.PlutusTx.Coordination.Contracts.PingPong (PingPongError, PingPongSchema)
import qualified Language.PlutusTx.Coordination.Contracts.PingPong as PingPong

import           Test.Tasty

theContract :: Contract PingPongSchema PingPongError ()
theContract = do
    _ <- PingPong.initialise
    PingPong.runPong
    PingPong.runPing
    PingPong.runPong

w1 :: Wallet
w1 = Wallet 1

tests :: TestTree
tests = testGroup "pingpong"
    [ checkPredicate "activate endpoints"
        theContract
        (endpointAvailable @"pong" w1)
        (callEndpoint @"initialise" w1 ()
        >> handleBlockchainEvents w1
        >> addBlocks 1
        >> handleBlockchainEvents w1
        >> callEndpoint @"pong" w1 ()
        >> handleBlockchainEvents w1
        >> addBlocks 1
        >> handleBlockchainEvents w1
        >> callEndpoint @"ping" w1 ()
        >> handleBlockchainEvents w1
        >> addBlocks 1
        >> handleBlockchainEvents w1
        )

    ]
