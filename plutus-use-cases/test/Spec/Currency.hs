{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE OverloadedStrings #-}
module Spec.Currency(tests) where

import           Language.Plutus.Contract
import           Language.Plutus.Contract.Test
import qualified Ledger

import           Language.PlutusTx.Coordination.Contracts.Currency (Currency)
import qualified Language.PlutusTx.Coordination.Contracts.Currency as Cur

import           Test.Tasty

tests :: TestTree
tests = testGroup "currency"
    [ checkPredicate "can create a new currency"
        theContract
        (assertDone w1 (const True) "currency contract not done")
        (handleBlockchainEvents (Wallet 1) >> addBlocks 1 >> handleBlockchainEvents (Wallet 1) >> addBlocks 1 >> handleBlockchainEvents (Wallet 1))

    , checkPredicate "script size is reasonable"
        theContract
        (assertDone w1 ((25000 >=) . Ledger.scriptSize . Ledger.unMonetaryPolicyScript . Cur.curPolicy) "script too large")
        (handleBlockchainEvents (Wallet 1) >> addBlocks 1 >> handleBlockchainEvents (Wallet 1) >> addBlocks 1 >> handleBlockchainEvents (Wallet 1))

    ]

w1 :: Wallet
w1 = Wallet 1

theContract :: Contract BlockchainActions Cur.CurrencyError Currency
theContract =
    let amounts = [("my currency", 1000), ("my token", 1)] in
    Cur.forgeContract (Ledger.pubKeyHash $ walletPubKey w1) amounts
