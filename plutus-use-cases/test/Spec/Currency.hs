{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE OverloadedStrings #-}
module Spec.Currency(tests, currencyTrace) where

import           Control.Monad                                     (void)
import           Language.Plutus.Contract
import           Language.Plutus.Contract.Test
import qualified Ledger

import           Language.PlutusTx.Coordination.Contracts.Currency (Currency)
import qualified Language.PlutusTx.Coordination.Contracts.Currency as Cur
import qualified Plutus.Trace.Emulator                             as Trace

import           Test.Tasty

-- | Runs 'Language.PlutusTx.Coordination.Contracts.Currency.forgeContract' for
--   a sample currency.
currencyTrace :: Trace.EmulatorTrace ()
currencyTrace = do
    _ <- Trace.activateContractWallet w1 (void theContract)
    _ <- Trace.nextSlot
    void $ Trace.nextSlot

tests :: TestTree
tests = testGroup "currency"
    [ checkPredicate
        "can create a new currency"
        (assertDone theContract (Trace.walletInstanceTag w1) (const True) "currency contract not done")
        currencyTrace

    , checkPredicate
        "script size is reasonable"
        (assertDone theContract (Trace.walletInstanceTag w1) ((30000 >=) . Ledger.scriptSize . Ledger.unMonetaryPolicyScript . Cur.curPolicy) "script too large")
        currencyTrace

    ]

w1 :: Wallet
w1 = Wallet 1

theContract :: Contract () BlockchainActions Cur.CurrencyError Currency
theContract =
    let amounts = [("my currency", 1000), ("my token", 1)] in
    Cur.forgeContract (Ledger.pubKeyHash $ walletPubKey w1) amounts
