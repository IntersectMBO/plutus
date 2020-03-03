{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
module Spec.MultiSig(tests) where

import           Data.Text (Text)

import           Language.Plutus.Contract.Test
import           Wallet.Emulator.SigningProcess                  (signWallets)
import qualified Ledger.Ada                                      as Ada
import           Ledger.Index                                    (ValidationError(ScriptFailure))
import           Ledger.Scripts                                  (ScriptError(EvaluationError))
import           Wallet.Emulator                                 (walletPubKey, Wallet(..))
import           Language.PlutusTx.Coordination.Contracts.MultiSig as MS
import qualified Ledger
import qualified Language.PlutusTx                                 as PlutusTx

import           Test.Tasty
import qualified Spec.Lib                                        as Lib
import           Prelude                                         hiding (not)

tests :: TestTree
tests = testGroup "multisig"
    [ checkPredicate @MultiSigSchema @Text "2 out of 5"
        MS.contract
        (assertFailedTransaction (\_ err -> case err of {ScriptFailure (EvaluationError ["not enough signatures"]) -> True; _ -> False  }))
        (callEndpoint @"lock" w1 (multiSig, Ada.lovelaceValueOf 10)
        >> handleBlockchainEvents w1
        >> callEndpoint @"unlock" w1 (multiSig, fmap (Ledger.pubKeyHash . walletPubKey) [w1, w2])
        >> setSigningProcess w1 (signWallets [w1, w2])
        >> handleBlockchainEvents w1
        )

    , checkPredicate @MultiSigSchema @Text "3 out of 5"
        MS.contract
        assertNoFailedTransactions
        (callEndpoint @"lock" w1 (multiSig, Ada.lovelaceValueOf 10)
        >> handleBlockchainEvents w1
        >> callEndpoint @"unlock" w1 (multiSig, fmap (Ledger.pubKeyHash . walletPubKey) [w1, w2, w3])
        >> setSigningProcess w1 (signWallets [w1, w2, w3])
        >> handleBlockchainEvents w1
        )

    , Lib.goldenPir "test/Spec/multisig.pir" $$(PlutusTx.compile [|| MS.validate ||])
    ]

w1, w2, w3 :: Wallet
w1 = Wallet 1
w2 = Wallet 2
w3 = Wallet 3

-- a 'MultiSig' contract that requires three out of five signatures
multiSig :: MultiSig
multiSig = MultiSig
        { signatories = Ledger.pubKeyHash . walletPubKey . Wallet <$> [1..5]
        , minNumSignatures = 3
        }
