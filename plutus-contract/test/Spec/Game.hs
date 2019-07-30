{-# LANGUAGE FlexibleContexts #-}
module Spec.Game where

import qualified Data.Aeson                                    as Aeson
import           Test.Tasty

import qualified Language.Plutus.Contract.Prompt.Event         as Event
import qualified Ledger.Ada                                    as Ada
import qualified Wallet.Emulator                               as EM

import           Examples.Game                                 (GuessParams (..), LockParams (..), game)
import           Language.PlutusTx.Coordination.Contracts.Game (gameAddress)

import           Spec.HUnit

tests :: TestTree
tests = testGroup "game"
    [ checkPredicate "Expose 'lock' endpoint and watch game address"
        game
        (endpointAvailable w1 "lock" <> interestingAddress w1 gameAddress)
        $ pure ()

    , checkPredicate "'lock' endpoint submits a transaction"
        game
        (anyTx w1)
        $ addEvent w1 (Event.endpoint "lock" (Aeson.toJSON $ LockParams "secret" 10))

    , checkPredicate "'guess' endpoint is available after locking funds"
        game
        (endpointAvailable w2 "guess")
        $ callEndpoint w1 "lock" (LockParams "secret" 10)
            >> notifyInterestingAddresses w2
            >> handleBlockchainEvents w1

    , checkPredicate "unlock funds"
        game
        (walletFundsChange w2 (Ada.adaValueOf 10)
            <> walletFundsChange w1 (Ada.adaValueOf (-10)))
        $ callEndpoint w1 "lock" (LockParams "secret" 10)
            >> notifyInterestingAddresses w2
            >> handleBlockchainEvents w1
            >> callEndpoint w2 "guess" (GuessParams "secret")
            >> handleBlockchainEvents w2
    ]

w1, w2 :: EM.Wallet
w1 = EM.Wallet 1
w2 = EM.Wallet 2
