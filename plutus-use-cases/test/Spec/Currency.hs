{-# LANGUAGE FlexibleContexts #-}
module Spec.Currency(tests) where

import           Control.Monad                                     (replicateM_, void)

import           Language.Plutus.Contract
import           Language.Plutus.Contract.Test
import           Language.PlutusTx.Lattice
import qualified Ledger

import           Wallet.Emulator                                   (walletPubKey)

import           Language.PlutusTx.Coordination.Contracts.Currency (Currency)
import qualified Language.PlutusTx.Coordination.Contracts.Currency as Cur


import           Test.Tasty

tests :: TestTree
tests = testGroup "currency"
    [ checkPredicate "can create a new currency"
        theContract
        (assertDone w1 (const True) "currency contract not done")
        (replicateM_ 6 (handleBlockchainEvents (Wallet 1)))

    , checkPredicate "script size is reasonable"
        theContract
        (assertDone w1 ((50000 >=) . Ledger.scriptSize . Ledger.getValidator . Cur.curValidator) "script too large")
        (replicateM_ 6 (handleBlockchainEvents (Wallet 1)))

    ]

w1 :: Wallet
w1 = Wallet 1

theContract :: Contract BlockchainActions Currency
theContract =
    let amounts = [("my currency", 1000), ("my token", 1)] in
    Cur.forgeContract (walletPubKey w1) amounts
