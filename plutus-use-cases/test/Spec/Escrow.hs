{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE TypeApplications #-}
module Spec.Escrow where

import           Control.Monad                                   (void)

import           Language.Plutus.Contract
import           Language.Plutus.Contract.Test
import           Ledger                                          (pubKeyHash)
import qualified Ledger.Ada                                      as Ada
import qualified Ledger.Typed.Scripts                            as Scripts
import qualified Spec.Lib                                        as Lib

import           Wallet.Emulator                                 (walletPubKey)

import           Language.PlutusTx.Coordination.Contracts.Escrow
import           Language.PlutusTx.Lattice

import           Test.Tasty
import qualified Test.Tasty.HUnit                                as HUnit

tests :: TestTree
tests = testGroup "escrow"
    [ checkPredicate @EscrowSchema @EscrowError "can pay"
        (void $ payEp escrowParams)
        (assertDone w1 (const True) "escrow pay not done" /\ walletFundsChange w1 (Ada.lovelaceValueOf (-10)))
        (callEndpoint @"pay-escrow" w1 (Ada.lovelaceValueOf 10)
        >> handleBlockchainEvents w1)

    , checkPredicate @EscrowSchema @EscrowError "can redeem"
        (void $ selectEither (payEp escrowParams) (redeemEp escrowParams))
        ( assertDone w3 (const True) "escrow redeem not done"
          /\ walletFundsChange w1 (Ada.lovelaceValueOf (-10))
          /\ walletFundsChange w2  (Ada.lovelaceValueOf 10)
          /\ walletFundsChange w3 mempty
        )
        ( callEndpoint @"pay-escrow" w1 (Ada.lovelaceValueOf 20)
        >> callEndpoint @"pay-escrow" w2 (Ada.lovelaceValueOf 10)
        >> handleBlockchainEvents w1
        >> handleBlockchainEvents w2
        >> callEndpoint @"redeem-escrow" w3 ()
        >> notifySlot w3
        >> handleBlockchainEvents w3
        >> handleBlockchainEvents w1
        >> handleBlockchainEvents w2)

    , checkPredicate @EscrowSchema @EscrowError "can redeem even if more money than required has been paid in"
          (both (payEp escrowParams) (redeemEp escrowParams))

          -- in this test case we pay in a total of 40 lovelace (10 more than required), for
          -- the same contract as before, requiring 10 lovelace to go to wallet 1 and 20 to
          -- wallet 2.
          --
          -- The scenario is
          -- * Wallet 1 contributes 20
          -- * Wallet 2 contributes 10
          -- * Wallet 3 contributes 10
          -- * Wallet 1 is going to redeem the payments
          --

          -- Wallet 1 pays 20 and receives 10 from the escrow contract and another 10
          -- in excess inputs
          ( walletFundsChange w1 (Ada.lovelaceValueOf 0)

          -- Wallet 2 pays 10 and receives 20, as per the contract.
            /\ walletFundsChange w2 (Ada.lovelaceValueOf 10)

          -- Wallet 3 pays 10 and doesn't receive anything.
            /\ walletFundsChange w3 (Ada.lovelaceValueOf (-10))
          )

          ( callEndpoint @"pay-escrow" w1 (Ada.lovelaceValueOf 20)
          >> callEndpoint @"pay-escrow" w2 (Ada.lovelaceValueOf 10)
          >> callEndpoint @"pay-escrow" w3 (Ada.lovelaceValueOf 10)
          >> handleBlockchainEvents w1
          >> handleBlockchainEvents w2
          >> handleBlockchainEvents w3
          >> callEndpoint @"redeem-escrow" w1 ()
          >> notifySlot w1
          >> handleBlockchainEvents w1
          >> handleBlockchainEvents w3
          >> handleBlockchainEvents w2)

    , checkPredicate @EscrowSchema @EscrowError "can refund"
        (payEp escrowParams >> refundEp escrowParams)
        ( walletFundsChange w1 mempty
          /\ assertDone w1 (const True) "refund should succeed")
        ( callEndpoint @"pay-escrow" w1 (Ada.lovelaceValueOf 20)
        >> handleBlockchainEvents w1
        >> addBlocks 200
        >> callEndpoint @"refund-escrow" w1 ()
        >> handleBlockchainEvents w1)

    , HUnit.testCase "script size is reasonable" (Lib.reasonable (Scripts.validatorScript $ scriptInstance escrowParams) 35000)
    ]

w1, w2, w3 :: Wallet
w1 = Wallet 1
w2 = Wallet 2
w3 = Wallet 3

escrowParams :: EscrowParams d
escrowParams =
  EscrowParams
    { escrowDeadline = 200
    , escrowTargets  =
        [ payToPubKeyTarget (pubKeyHash $ walletPubKey w1) (Ada.lovelaceValueOf 10)
        , payToPubKeyTarget (pubKeyHash $ walletPubKey w2) (Ada.lovelaceValueOf 20)
        ]
    }
