{-# LANGUAGE FlexibleContexts #-}
module Spec.MultiSigStateMachine(tests) where

import           Control.Monad                                                 (foldM, void, (>=>))
import           Control.Monad.Except                                          (throwError)
import           Data.Either                                                   (isLeft, isRight)
import           Data.Foldable                                                 (traverse_)
import qualified Data.Map                                                      as Map
import qualified Data.Text                                                     as Text
import qualified Spec.Size                                                     as Size
import           Test.Tasty                                                    (TestTree, testGroup)
import qualified Test.Tasty.HUnit                                              as HUnit

import qualified Ledger.Ada                                                    as Ada
import           Ledger.Value                                                  (Value)
import           Wallet.API                                                    (WalletAPI,
                                                                                WalletDiagnostics)
import qualified Wallet.Emulator                                               as EM

import           Language.PlutusTx.Coordination.Contracts.MultiSigStateMachine (Payment, State)
import qualified Language.PlutusTx.Coordination.Contracts.MultiSigStateMachine as MS

tests :: TestTree
tests = testGroup "multi sig state machine tests" [
    HUnit.testCaseSteps "lock, propose, sign 3x, pay - SUCCESS" (runTrace (lockProposeSignPay 3) isRight),
    HUnit.testCaseSteps "lock, propose, sign 2x, pay - FAILURE" (runTrace (lockProposeSignPay 2) isLeft),
    HUnit.testCase "script size is reasonable" (Size.reasonable (MS.validator params) 330000)
    ]

runTrace :: EM.EmulatorAction a -> (Either EM.AssertionError a -> Bool) -> (String -> IO ()) -> IO ()
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

lockProposeSignPay :: (EM.MonadEmulator m) => Int -> m ()
lockProposeSignPay i = do

    let getResult = EM.processEmulated >=> extract where
        extract = either (throwError . EM.AssertionError . Text.pack . show) pure . fst

    -- stX contain the state of the contract. See note [Current state of the 
    -- contract] in 
    -- Language.PlutusTx.Coordination.Contracts.MultiSigStateMachine
    st1 <- getResult $ do
        processAndNotify

        -- instruct all three wallets to start watching the contract address
        traverse_ (\w -> EM.walletAction w initialise') [w1, w2, w3]
        processAndNotify

        -- wallet 1 locks the funds
        EM.runWalletAction w1 (lock' (Ada.adaValueOf 10))

    -- wallet 2 proposes the payment
    st2 <- getResult $ do
        processAndNotify
        EM.runWalletAction w2 (proposePayment' st1 payment)

    -- i wallets add their signatures
    st3 <- foldM (\st w -> getResult (processAndNotify >> EM.runWalletAction w (addSignature' st))) st2 (take i [w1, w2, w3])

    EM.processEmulated $ do
        processAndNotify
        void $ EM.walletAction w3 (makePayment' st3)
        processAndNotify
        EM.assertOwnFundsEq w2 (Ada.adaValueOf 5)
