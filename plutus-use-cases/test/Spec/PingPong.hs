{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE TypeApplications #-}
module Spec.PingPong(tests) where

import           Data.Maybe                                        (isNothing)
import           Language.Plutus.Contract
import           Language.Plutus.Contract.Test
import           Language.PlutusTx.Lattice

import           Language.Plutus.Contract.StateMachine             (OnChainState)
import           Language.PlutusTx.Coordination.Contracts.PingPong (Input, PingPongError, PingPongSchema, PingPongState)
import qualified Language.PlutusTx.Coordination.Contracts.PingPong as PingPong

import           Test.Tasty

theContract :: Contract PingPongSchema PingPongError ()
theContract = do
    _ <- PingPong.initialise
    PingPong.runPong
    PingPong.runPing
    PingPong.runPong

twoParties :: Contract PingPongSchema PingPongError (Maybe (OnChainState PingPongState Input))
twoParties =
    -- one party calls "initialise"
    -- the other party calls "stop"
    -- then the first party will learn that the instance has
    -- terminated when 'runWaitForUpdate' returns 'Nothing'.
    let p1 = PingPong.initialise >> PingPong.runWaitForUpdate
        p2 = PingPong.runStop
    in p1 `select` fmap (const Nothing) p2

w1, w2 :: Wallet
w1 = Wallet 1
w2 = Wallet 2

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
    , checkPredicate "Stop the contract"
        twoParties
        (assertDone w1 isNothing ""
        /\ assertDone w2 isNothing ""
        )
        (callEndpoint @"initialise" w1 ()
        >> handleBlockchainEvents w1
        >> addBlocks 1
        >> handleBlockchainEvents w1
        >> callEndpoint @"stop" w2 ()
        >> handleBlockchainEvents w2
        >> addBlocks 1
        >> handleBlockchainEvents w1
        >> handleBlockchainEvents w2
        )


    ]
