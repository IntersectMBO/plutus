{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE MonoLocalBinds      #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeApplications    #-}

{-# OPTIONS_GHC -fno-strictness  #-}
{-# OPTIONS_GHC -fno-ignore-interface-pragmas #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:debug-context #-}

module Spec.MultiSigStateMachine(tests, lockProposeSignPay) where

import           Data.Foldable                         (traverse_)

import qualified Ledger
import qualified Ledger.Ada                            as Ada
import           Ledger.Time                           (POSIXTime)
import qualified Ledger.TimeSlot                       as TimeSlot
import qualified Ledger.Typed.Scripts                  as Scripts
import qualified Wallet.Emulator                       as EM

import           Plutus.Contract.Test
import qualified Plutus.Contracts.MultiSigStateMachine as MS
import           Plutus.Trace.Emulator                 (EmulatorTrace)
import qualified Plutus.Trace.Emulator                 as Trace
import qualified PlutusTx

import           Test.Tasty                            (TestTree, testGroup)
import qualified Test.Tasty.HUnit                      as HUnit

tests :: TestTree
tests =
    testGroup "multi sig state machine tests"
    [ checkPredicate "lock, propose, sign 3x, pay - SUCCESS"
        (assertNoFailedTransactions
        .&&. walletFundsChange w1 (Ada.lovelaceValueOf (-10))
        .&&. walletFundsChange w2 (Ada.lovelaceValueOf 5))
        (lockProposeSignPay 3 1)

    , checkPredicate "lock, propose, sign 2x, pay - FAILURE"
        (assertNotDone (MS.contract  @MS.MultiSigError params) (Trace.walletInstanceTag w1) "contract should proceed after invalid transition"
        .&&. walletFundsChange w1 (Ada.lovelaceValueOf (-10))
        .&&. walletFundsChange w2 (Ada.lovelaceValueOf 0))
        (lockProposeSignPay 2 1)

    , checkPredicate "lock, propose, sign 3x, pay x2 - SUCCESS"
        (assertNoFailedTransactions
        .&&. walletFundsChange w1 (Ada.lovelaceValueOf (-10))
        .&&. walletFundsChange w2 (Ada.lovelaceValueOf 10))
        (lockProposeSignPay 3 2)

    , checkPredicate "lock, propose, sign 3x, pay x3 - FAILURE"
        (assertNotDone (MS.contract  @MS.MultiSigError params) (Trace.walletInstanceTag w2) "contract should proceed after invalid transition"
        .&&. walletFundsChange w1 (Ada.lovelaceValueOf (-10))
        .&&. walletFundsChange w2 (Ada.lovelaceValueOf 10))
        (lockProposeSignPay 3 3)

    , goldenPir "test/Spec/multisigStateMachine.pir" $$(PlutusTx.compile [|| MS.mkValidator ||])
    , HUnit.testCaseSteps "script size is reasonable" $ \step -> reasonable' step (Scripts.validatorScript $ MS.typedValidator params) 51000
    ]

-- | A multisig contract that requires 3 out of 5 signatures
params :: MS.Params
params = MS.Params keys 3 where
    keys = Ledger.pubKeyHash . EM.walletPubKey . knownWallet <$> [1..5]

-- | A payment of 5 Ada to the public key address of wallet 2
payment :: POSIXTime -> MS.Payment
payment startTime =
    MS.Payment
        { MS.paymentAmount    = Ada.lovelaceValueOf 5
        , MS.paymentRecipient = Ledger.pubKeyHash $ EM.walletPubKey w2
        , MS.paymentDeadline  = startTime + 20000
        }

-- | Lock some funds in the contract, then propose the payment
--   'payment', then call @"add-signature"@ a number of times and
--   finally call @"pay"@ a number of times.
lockProposeSignPay :: Integer -> Integer -> EmulatorTrace ()
lockProposeSignPay signatures rounds = do
    let wallets = knownWallet <$> [1..signatures]
        activate w = Trace.activateContractWallet w (MS.contract @MS.MultiSigError params)

    -- the 'proposeSignPay' trace needs at least 2 signatures
    handle1 <- activate w1
    handle2 <- activate w2
    handles <- traverse activate (drop 2 wallets)
    _ <- Trace.callEndpoint @"lock" handle1 (Ada.lovelaceValueOf 10)
    _ <- Trace.waitNSlots 1
    startTime <- TimeSlot.scSlotZeroTime <$> Trace.getSlotConfig
    let proposeSignPay = do
            Trace.callEndpoint @"propose-payment" handle2 (payment startTime)
            _ <- Trace.waitNSlots 1
            -- Call @"add-signature"@ @signatures@ times
            traverse_ (\hdl -> Trace.callEndpoint @"add-signature" hdl () >> Trace.waitNSlots 1) (handle1:handle2:handles)

            -- Call @"pay"@ on wallet 1
            Trace.callEndpoint @"pay" handle1 ()
            Trace.waitNSlots 1

    traverse_ (const proposeSignPay) [1..rounds]
