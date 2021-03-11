{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TemplateHaskell  #-}
{-# LANGUAGE TypeApplications #-}
module Spec.MultiSig(tests, failingTrace, succeedingTrace) where

import           Control.Monad             (void)
import qualified Ledger
import qualified Ledger.Ada                as Ada
import           Ledger.Index              (ValidationError (ScriptFailure))
import           Ledger.Scripts            (ScriptError (EvaluationError))
import           Plutus.Contract           (Contract, ContractError)
import           Plutus.Contract.Test
import           Plutus.Contracts.MultiSig as MS
import           Plutus.Trace.Emulator     (EmulatorTrace)
import qualified Plutus.Trace.Emulator     as Trace
import qualified PlutusTx                  as PlutusTx
import           Prelude                   hiding (not)
import qualified Spec.Lib                  as Lib
import           Test.Tasty
import           Wallet.Emulator.Wallet    (signWallets)

tests :: TestTree
tests = testGroup "multisig"
    [ checkPredicate "2 out of 5"
        (assertFailedTransaction (\_ err _ -> case err of {ScriptFailure (EvaluationError ["not enough signatures"]) -> True; _ -> False  }))
        failingTrace

    , checkPredicate "3 out of 5"
        assertNoFailedTransactions
        succeedingTrace

    , Lib.goldenPir "test/Spec/multisig.pir" $$(PlutusTx.compile [|| MS.validate ||])
    ]

-- | Lock some funds, then attempt to unlock them with a transaction
--   that doesn't have the required number of signatures
failingTrace :: EmulatorTrace ()
failingTrace = do
    hdl <- Trace.activateContractWallet w1 theContract
    Trace.callEndpoint @"lock" hdl (multiSig, Ada.lovelaceValueOf 10)
    _ <- Trace.waitNSlots 1
    Trace.setSigningProcess w1 (signWallets [w1, w2])
    Trace.callEndpoint @"unlock" hdl (multiSig, fmap (Ledger.pubKeyHash . walletPubKey) [w1, w2])
    void $ Trace.waitNSlots 1

-- | Lock some funds, then unlock them with a transaction that has the
--   three required signatures.
succeedingTrace :: EmulatorTrace ()
succeedingTrace = do
    hdl <- Trace.activateContractWallet w1 theContract
    Trace.callEndpoint @"lock" hdl (multiSig, Ada.lovelaceValueOf 10)
    _ <- Trace.waitNSlots 1
    Trace.setSigningProcess w1 (signWallets [w1, w2, w3])
    Trace.callEndpoint @"unlock" hdl (multiSig, fmap (Ledger.pubKeyHash . walletPubKey) [w1, w2, w3])
    void $ Trace.waitNSlots 1

w1, w2, w3 :: Wallet
w1 = Wallet 1
w2 = Wallet 2
w3 = Wallet 3

theContract :: Contract () MultiSigSchema ContractError ()
theContract = MS.contract

-- a 'MultiSig' contract that requires three out of five signatures
multiSig :: MultiSig
multiSig = MultiSig
        { signatories = Ledger.pubKeyHash . walletPubKey . Wallet <$> [1..5]
        , minNumSignatures = 3
        }
