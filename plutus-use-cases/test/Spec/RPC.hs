{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE LambdaCase       #-}
{-# LANGUAGE TypeApplications #-}
module Spec.RPC(tests) where

import           Data.Either                                  (isRight)
import           Language.Plutus.Contract
import           Language.Plutus.Contract.Test
import           Language.PlutusTx.Lattice
import           Wallet.Emulator.Notify                       (walletInstanceId)

import           Language.PlutusTx.Coordination.Contracts.RPC

import           Test.Tasty

theContract :: Contract AdderSchema AdderError (Either (Either CancelRPC Integer) ())
theContract = callAdder `selectEither` respondAdder

cancelContract :: Contract AdderSchema AdderError (Either (Either CancelRPC Integer) ())
cancelContract = callAdderCancel `selectEither` respondAdder

server, client :: Wallet
server = Wallet 1
client = Wallet 2

tests :: TestTree
tests = testGroup "RPC"
    [ checkPredicate "call RPC"
        theContract
        (assertDone server isRight ""
        /\ assertDone client (\case { Left (Right 4) -> True; _ -> False}) "")
        (callEndpoint @"serve" server ()
        >> handleBlockchainEvents server
        >> callEndpoint @"target instance" client (walletInstanceId server)
        >> handleBlockchainEvents server
        >> handleBlockchainEvents client
        >> handleBlockchainEvents server
        >> handleBlockchainEvents client
        )
    , checkPredicate "call RPC with error"
        cancelContract
        (assertDone server isRight ""
        /\ assertDone client (\case { Left (Left CancelRPC) -> True; _ -> False}) "")
        (callEndpoint @"serve" server ()
        >> handleBlockchainEvents server
        >> callEndpoint @"target instance" client (walletInstanceId server)
        >> handleBlockchainEvents server
        >> handleBlockchainEvents client
        >> handleBlockchainEvents server
        >> handleBlockchainEvents client
        )

    ]
