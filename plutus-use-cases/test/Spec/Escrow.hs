{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE LambdaCase       #-}
{-# LANGUAGE TypeApplications #-}
module Spec.Escrow where

import           Control.Monad                                   (void)

import           Language.Plutus.Contract
import           Language.Plutus.Contract.Test
import qualified Ledger.Ada                                      as Ada
import qualified Spec.Lib                                        as Lib

import           Wallet.Emulator                                 (walletPubKey)

import           Language.PlutusTx.Coordination.Contracts.Escrow
import           Language.PlutusTx.Lattice

import           Test.Tasty
import qualified Test.Tasty.HUnit                                as HUnit

tests :: TestTree
tests = testGroup "escrow"
    [ checkPredicate @EscrowSchema "can pay"
        (void $ payEp escrowParams)
        (assertDone w1 (const True) "escrow pay not done" /\ walletFundsChange w1 (Ada.lovelaceValueOf (-10)))
        (callEndpoint @"pay-escrow" (Wallet 1) (walletPubKey w1, Ada.lovelaceValueOf 10)
        >> handleBlockchainEvents (Wallet 1))

    , checkPredicate @EscrowSchema "can redeem"
        (void $ selectEither (payEp escrowParams) (redeemEp escrowParams))
        ( assertDone w3 (const True) "escrow redeem not done"
          /\ walletFundsChange w1 (Ada.lovelaceValueOf (-10))
          /\ walletFundsChange w2  (Ada.lovelaceValueOf 10)
          /\ walletFundsChange w3 mempty
        )
        ( callEndpoint @"pay-escrow" (Wallet 1) (walletPubKey w1, Ada.lovelaceValueOf 20)
        >> callEndpoint @"pay-escrow" (Wallet 2) (walletPubKey w2, Ada.lovelaceValueOf 10)
        >> handleBlockchainEvents (Wallet 1)
        >> handleBlockchainEvents (Wallet 2)
        >> callEndpoint @"redeem-escrow" (Wallet 3) ()
        >> notifySlot w3
        >> handleUtxoQueries (Wallet 3)
        >> handleBlockchainEvents (Wallet 3)
        >> handleBlockchainEvents (Wallet 1)
        >> handleBlockchainEvents (Wallet 2))

    , checkPredicate @EscrowSchema "can refund"
        (payEp escrowParams >>= refundEp escrowParams)
        ( walletFundsChange w1 mempty
          /\ assertDone w1 (\case { RefundOK _ -> True; _ -> False}) "refund should succeed")
        ( callEndpoint @"pay-escrow" (Wallet 1) (walletPubKey w1, Ada.lovelaceValueOf 20)
        >> handleBlockchainEvents (Wallet 1)
        >> addBlocks 200
        >> callEndpoint @"refund-escrow" (Wallet 1) ()
        >> handleUtxoQueries (Wallet 1)
        >> handleBlockchainEvents (Wallet 1))

    , HUnit.testCase "script size is reasonable" (Lib.reasonable (escrowScript escrowParams) 50000)
    ]

w1, w2, w3 :: Wallet
w1 = Wallet 1
w2 = Wallet 2
w3 = Wallet 3

escrowParams :: EscrowParams
escrowParams =
  EscrowParams
    { escrowDeadline = 200
    , escrowTargets  =
        [ payToPubKeyTarget (walletPubKey w1) (Ada.lovelaceValueOf 10)
        , payToPubKeyTarget (walletPubKey w2) (Ada.lovelaceValueOf 20)
        ]
    }

