{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE ExplicitForAll    #-}
{-# LANGUAGE NumericUnderscores  #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications  #-}
{-# OPTIONS_GHC -fno-warn-incomplete-uni-patterns
-fno-warn-name-shadowing
-fno-warn-unused-do-bind
-fno-warn-unused-top-binds #-}
module Spec.Marlowe.Marlowe2
    ( tests
    )
where

import           Test.Tasty

import           Language.Marlowe.Semantics
import           Language.Marlowe.Util
import           Language.Marlowe.Client2
import           Language.Plutus.Contract hiding (Contract)
import           Language.Plutus.Contract.Test
import qualified Language.Plutus.Contract.Effects.OwnPubKey        as OwnPubKey
import qualified Wallet.Emulator.Wallet                            as EM
import           Language.PlutusTx.Lattice
import           Ledger
import           Ledger.Ada                 (adaValueOf)


tests :: TestTree
tests = testGroup "token account"
    [ checkPredicate @MarloweSchema @ContractError "Create a Marlowe Contract" marloweContract2
        (assertNoFailedTransactions
        /\ assertNotDone w1 "contract should not have any errors"
        -- /\ walletFundsChange w1 (Ada.adaValueOf (-1))
        )
        (  callEndpoint @"create" w1 (Close)
           >> handleBlockchainEvents w1 )
    , zeroCouponBondTest
    ]


zeroCouponBondTest :: TestTree
zeroCouponBondTest = checkPredicate @MarloweSchema @ContractError "ZCB" marloweContract2
    (assertNoFailedTransactions
    /\ emulatorLog (const False) ""
    /\ assertDone w1 (const True) "contract should close"
    /\ walletFundsChange bob (adaValueOf (-150))
    /\ walletFundsChange alice (adaValueOf (150))
    ) $ do
    -- Init a contract
    let alicePk = pubKeyHash $ walletPubKey alice
        aliceAcc = AccountId 0 alicePk
        bobPk = pubKeyHash $ walletPubKey bob

    let zeroCouponBond = When [ Case
            (Deposit aliceAcc alicePk ada (Constant 850_000_000))
            (Pay aliceAcc (Party bobPk) ada (Constant 850_000_000)
                (When
                    [ Case (Deposit aliceAcc bobPk ada (Constant 1000_000_000))
                        (Pay aliceAcc (Party alicePk) ada (Constant 1000_000_000)
                        Close)
                    ] (Slot 200) Close
                ))] (Slot 100) Close

    callEndpoint @"create" alice zeroCouponBond
    notifyInterestingAddresses alice
    notifyInterestingAddresses bob
    addBlocks 10
    handleBlockchainEvents alice
    handleBlockchainEvents bob
    notifySlot alice
    notifySlot bob
    -- callEndpoint @"sub" alice (alicePk)
    -- callEndpoint @"sub" bob (alicePk)
    callEndpoint @"apply-inputs" alice (alicePk, [IDeposit aliceAcc alicePk ada 850_000_000])
    notifyInterestingAddresses alice
    notifyInterestingAddresses bob
    addBlocks 10
    handleBlockchainEvents alice
    handleBlockchainEvents bob
    notifySlot alice
    notifySlot bob
    -- callEndpoint @"sub" alice (alicePk)
    -- callEndpoint @"sub" bob (alicePk)
    callEndpoint @"apply-inputs" bob (alicePk, [IDeposit aliceAcc bobPk ada 1000_000_000])
    handleBlockchainEvents alice
    handleBlockchainEvents bob
    notifySlot alice
    notifySlot bob



w1, w2 :: Wallet
w1 = Wallet 1
w2 = Wallet 2

alice, bob, carol :: Wallet
alice = Wallet 1
bob = Wallet 2
carol = Wallet 3
