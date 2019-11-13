{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE TypeApplications         #-}
{-# LANGUAGE ScopedTypeVariables         #-}
{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -fno-strictness #-}
{-# OPTIONS_GHC -fno-ignore-interface-pragmas #-}
{-# OPTIONS -fplugin-opt Language.PlutusTx.Plugin:debug-context #-}
module Spec.MultiSigStateMachine(tests) where

import           Control.Monad                                                 (foldM, foldM_, void, (>=>))
import           Data.Either                                                   (isLeft, isRight)
import           Data.Foldable                                                 (traverse_)
import qualified Data.Map                                                      as Map
import           Test.Tasty                                                    (TestTree, testGroup)
import qualified Test.Tasty.HUnit                                              as HUnit

import           Spec.Lib                                                      as Lib

import qualified Ledger.Ada                                                    as Ada
import qualified Ledger.Typed.Scripts                                          as Scripts
import           Ledger.Value                                                  (Value, scale)
import           Wallet.API                                                    (WalletAPI,
                                                                                WalletDiagnostics)
import qualified Wallet.Emulator                                               as EM

import qualified Language.PlutusTx as PlutusTx

import           Language.PlutusTx.Coordination.Contracts.MultiSigStateMachine (Payment, State)
import qualified Language.PlutusTx.Coordination.Contracts.MultiSigStateMachine as MS

tests :: TestTree
tests = testGroup "multi sig state machine tests" [
    HUnit.testCaseSteps "lock, propose, sign 3x, pay - SUCCESS" (runTrace (lockProposeSignPay 3 1) isRight),
    HUnit.testCaseSteps "lock, propose, sign 2x, pay - FAILURE" (runTrace (lockProposeSignPay 2 1) isLeft),
    HUnit.testCaseSteps "lock, propose, sign 3x, pay x2 - SUCCESS" (runTrace (lockProposeSignPay 3 2) isRight),
    HUnit.testCaseSteps "lock, propose, sign 3x, pay x3 - FAILURE" (runTrace (lockProposeSignPay 3 3) isLeft),
    Lib.goldenPir "test/Spec/multisigStateMachine.pir" $$(PlutusTx.compile [|| MS.mkValidator ||]),
    HUnit.testCase "script size is reasonable" (Lib.reasonable (Scripts.validatorScript $ MS.scriptInstance params) 50000)
    ]

runTrace :: EM.EmulatorAction EM.AssertionError a -> (Either EM.AssertionError a -> Bool) -> (String -> IO ()) -> IO ()
runTrace t f step = do
    let initialState = EM.emulatorStateInitialDist (Map.singleton (EM.walletPubKey (EM.Wallet 1)) (Ada.adaValueOf 10))
        (result, st) = EM.runEmulator initialState t
    if f result
    then pure ()
    else do
        step (show $ EM.emLog st)
        HUnit.assertFailure "transaction failed to validate"

processAndNotify :: EM.Trace m ()
processAndNotify = void (EM.addBlocksAndNotify [w1, w2, w3] 1)

w1, w2, w3 :: EM.Wallet
w1 = EM.Wallet 1
w2 = EM.Wallet 2
w3 = EM.Wallet 3

-- | A multisig contract that requires 3 out of 5 signatures
params :: MS.Params
params = MS.Params keys 3 where
    keys = EM.walletPubKey . EM.Wallet <$> [1..5]

-- | A payment of 5 Ada to the public key address of wallet 2
payment :: MS.Payment
payment =
    MS.Payment
        { MS.paymentAmount    = Ada.adaValueOf 5
        , MS.paymentRecipient = EM.walletPubKey w2
        , MS.paymentDeadline  = 20
        }

initialise' :: WalletAPI m => m ()
initialise' = MS.initialise params

-- State machine transitions partially applied to the 'payment' multisig contract

lock' :: (WalletAPI m, WalletDiagnostics m) => Value -> m State
lock' = MS.lock params

proposePayment' :: (WalletAPI m, WalletDiagnostics m) => State -> Payment -> m State
proposePayment' = MS.proposePayment params

addSignature' :: (WalletAPI m, WalletDiagnostics m) => State -> m State
addSignature' = MS.addSignature params

makePayment' :: (WalletAPI m, WalletDiagnostics m) => State -> m State
makePayment' = MS.makePayment params

initialise'' :: WalletAPI m => EM.Trace m ()
initialise'' =
    -- instruct all three wallets to start watching the contract address
    traverse_ (\w -> EM.walletAction w initialise') [w1, w2, w3]

lock'' :: (WalletAPI m, WalletDiagnostics m) => Value -> EM.Trace m State
-- wallet 1 locks the funds
lock'' value = processAndNotify >> fst <$> EM.walletAction w1 (lock' value)

proposePayment'' :: (WalletAPI m, WalletDiagnostics m) => State -> EM.Trace m State
proposePayment'' st = processAndNotify >> fst <$> EM.walletAction w2 (proposePayment' st payment)

addSignature'' :: (WalletAPI m, WalletDiagnostics m) => Integer -> State -> EM.Trace m State
-- i wallets add their signatures
addSignature'' i inSt = foldM (\st w -> (processAndNotify >> fst <$> EM.walletAction w (addSignature' st))) inSt (take (fromIntegral i) [w1, w2, w3])

makePayment'' :: (WalletAPI m, WalletDiagnostics m) => State -> EM.Trace m State
makePayment'' st = processAndNotify >> fst <$> EM.walletAction w3 (makePayment' st)

proposeSignPay :: (WalletAPI m, WalletDiagnostics m) => Integer -> State -> EM.Trace m State
proposeSignPay i = proposePayment'' >=> addSignature'' i >=> makePayment''

lockProposeSignPay :: forall e m . (EM.MonadEmulator e m) => Integer -> Integer -> m ()
lockProposeSignPay i j = EM.processEmulated $ do

    -- stX contain the state of the contract. See note [Current state of the
    -- contract] in
    -- Language.PlutusTx.Coordination.Contracts.MultiSigStateMachine
    initialise''
    st1 <- lock'' (Ada.adaValueOf 10)

    foldM_ (\st _ -> proposeSignPay i st) st1 [1..j]

    processAndNotify
    EM.assertOwnFundsEq w2 (scale j (Ada.adaValueOf 5))
