{-# LANGUAGE MonoLocalBinds      #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# OPTIONS_GHC -fno-strictness  #-}
{-# OPTIONS_GHC -fno-ignore-interface-pragmas #-}
{-# OPTIONS -fplugin-opt Language.PlutusTx.Plugin:debug-context #-}
module Spec.MultiSigStateMachine(tests) where

import           Data.Foldable                                   (traverse_)
import           Test.Tasty                                      (TestTree, testGroup)
import qualified Test.Tasty.HUnit                                as HUnit

import           Spec.Lib                                        as Lib

import           Language.PlutusTx.Lattice
import qualified Ledger
import qualified Ledger.Ada                                      as Ada
import           Ledger.Index                                    (ValidationError(ScriptFailure))
import           Ledger.Scripts                                  (ScriptError(EvaluationError))
import           Ledger.TxId                                     (TxId)
import qualified Ledger.Typed.Scripts                            as Scripts
import qualified Wallet.Emulator                                 as EM

import qualified Language.PlutusTx as PlutusTx
import           Language.Plutus.Contract.Test

import           Language.PlutusTx.Coordination.Contracts.MultiSigStateMachine (MultiSigSchema, MultiSigError)
import qualified Language.PlutusTx.Coordination.Contracts.MultiSigStateMachine as MS

tests :: TestTree
tests =
    testGroup "multi sig state machine tests"
    [ checkPredicate @MultiSigSchema @MultiSigError "lock, propose, sign 3x, pay - SUCCESS"
        (MS.contract params)
        (assertNoFailedTransactions
        /\ walletFundsChange w1 (Ada.lovelaceValueOf (-10))
        /\ walletFundsChange w2 (Ada.lovelaceValueOf 5))
        (lockProposeSignPay 3 1)

    , checkPredicate @MultiSigSchema @MultiSigError "lock, propose, sign 2x, pay - FAILURE"
        (MS.contract params)
        (assertFailedTransaction checkScriptError
        /\ walletFundsChange w1 (Ada.lovelaceValueOf (-10))
        /\ walletFundsChange w2 (Ada.lovelaceValueOf 0))
        (lockProposeSignPay 2 1)

    , checkPredicate @MultiSigSchema @MultiSigError "lock, propose, sign 3x, pay x2 - SUCCESS"
        (MS.contract params)
        (assertNoFailedTransactions
        /\ walletFundsChange w1 (Ada.lovelaceValueOf (-10))
        /\ walletFundsChange w2 (Ada.lovelaceValueOf 10))
        (lockProposeSignPay 3 2)

    , checkPredicate @MultiSigSchema @MultiSigError "lock, propose, sign 3x, pay x3 - FAILURE"
        (MS.contract params)
        (assertContractError w1 (\case { ContractError MS.MSStateMachineError{} -> True; _ -> False}) "contract should fail"
        /\ walletFundsChange w1 (Ada.lovelaceValueOf (-10))
        /\ walletFundsChange w2 (Ada.lovelaceValueOf 10))
        (lockProposeSignPay 3 3)

    , Lib.goldenPir "test/Spec/multisigStateMachine.pir" $$(PlutusTx.compile [|| MS.mkValidator ||])
    , HUnit.testCase "script size is reasonable" (Lib.reasonable (Scripts.validatorScript $ MS.scriptInstance params) 50000)
    ]

w1, w2, w3 :: EM.Wallet
w1 = EM.Wallet 1
w2 = EM.Wallet 2
w3 = EM.Wallet 3

-- | A multisig contract that requires 3 out of 5 signatures
params :: MS.Params
params = MS.Params keys 3 where
    keys = Ledger.pubKeyHash . EM.walletPubKey . EM.Wallet <$> [1..5]

checkScriptError :: TxId -> ValidationError -> Bool
checkScriptError _ = \case
    ScriptFailure (EvaluationError ["State transition invalid - checks failed"]) -> True
    _ -> False

-- | A payment of 5 Ada to the public key address of wallet 2
payment :: MS.Payment
payment =
    MS.Payment
        { MS.paymentAmount    = Ada.lovelaceValueOf 5
        , MS.paymentRecipient = Ledger.pubKeyHash $ EM.walletPubKey w2
        , MS.paymentDeadline  = 20
        }

-- | Lock some funds in the contract, then propose the payment
--   'payment', then call @"add-signature"@ a number of times and
--   finally call @"pay"@ a number of times.
lockProposeSignPay
    :: MonadEmulator (TraceError MultiSigError) m
    => Integer
    -> Integer
    -> ContractTrace MultiSigSchema MultiSigError m a ()
lockProposeSignPay signatures rounds = do
    callEndpoint @"lock" w1 (Ada.lovelaceValueOf 10)
    handleBlockchainEvents w1

    let proposeSignPay = do
            callEndpoint @"propose-payment" w2 payment
            handleBlockchainEvents w2

            -- Call @"add-signature"@ @signatures@ times
            traverse_ (\wllt -> callEndpoint @"add-signature" wllt () >> handleBlockchainEvents wllt) (EM.Wallet <$> [1..signatures])

            -- Call @"pay"@ on wallet 1
            callEndpoint @"pay" w1 ()
            handleBlockchainEvents w1

    traverse_ (\_ -> proposeSignPay) [1..rounds]
