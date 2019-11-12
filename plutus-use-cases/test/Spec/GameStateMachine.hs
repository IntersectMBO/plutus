{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE TypeApplications         #-}
module Spec.GameStateMachine(tests) where

import           Control.Monad                                             (void)
import qualified Data.Map                                                  as Map
import           Test.Tasty
import qualified Test.Tasty.HUnit                                          as HUnit

import qualified Spec.Lib                                                  as Lib

import qualified Language.PlutusTx as PlutusTx

import           Language.PlutusTx.Coordination.Contracts.GameStateMachine as G
import qualified Ledger.Ada                                                as Ada
import           Ledger.Value                                              (Value)
import qualified Ledger.Typed.Scripts                                      as Scripts
import qualified Wallet.API                                                as W
import qualified Wallet.Emulator                                           as EM

tests :: TestTree
tests =
    let initialState = EM.emulatorStateInitialDist
                        (Map.fromList [ ( EM.walletPubKey w1, initialVal)
                                      , ( EM.walletPubKey w2, initialVal)
                                      , ( EM.walletPubKey w3, initialVal) ])
        checkResult (result, st) step =
            case result of
                Left err  -> do
                    _ <- step (show $ EM.emLog st)
                    _ <- step (show err)
                    HUnit.assertFailure "own funds not equal"
                Right _ ->
                    Lib.reasonable (Scripts.validatorScript G.scriptInstance) 35000
    in
        testGroup "state machine tests" [
            HUnit.testCaseSteps "run a successful game trace"
                (checkResult (EM.runEmulator @EM.AssertionError initialState runGameSuccess)),
            HUnit.testCaseSteps "run a 2nd successful game trace"
                (checkResult (EM.runEmulator @EM.AssertionError initialState runGameSuccess2)),
            HUnit.testCaseSteps "run a failed trace"
                (checkResult (EM.runEmulator @EM.AssertionError initialState runGameFailure)),
            Lib.goldenPir "test/Spec/gameStateMachine.pir" $$(PlutusTx.compile [|| mkValidator ||])
        ]

initialVal :: Value
initialVal = Ada.adaValueOf 10

w1 :: EM.Wallet
w1 = EM.Wallet 1

w2 :: EM.Wallet
w2 = EM.Wallet 2

w3 :: EM.Wallet
w3 = EM.Wallet 3

processAndNotify :: EM.Trace m ()
processAndNotify = void (EM.addBlocksAndNotify [w1, w2, w3] 1)

-- Wallet 1 locks some funds using the secret "hello". Then wallet 1
-- transfers the token to wallet 2, and wallet 2 makes a correct guess
-- and locks the remaining funds using the secret "new secret".
runGameSuccess :: (EM.MonadEmulator e m) => m ()
runGameSuccess = void $ EM.processEmulated $ do
        processAndNotify
        _   <- EM.runWalletAction w1 G.startGame
        _   <- EM.runWalletAction w2 G.startGame
        processAndNotify
        _ <- EM.runWalletAction w1 (G.lock "hello" (Ada.adaValueOf 8))
        processAndNotify
        processAndNotify
        _ <- EM.runWalletAction w1 (W.payToPublicKey_ W.defaultSlotRange G.gameTokenVal (EM.walletPubKey w2))
        processAndNotify
        _ <- EM.runWalletAction w2 (guess "hello" "new secret" (Ada.adaValueOf 3) (Ada.adaValueOf 5))
        processAndNotify
        EM.assertOwnFundsEq w2 (initialVal <> Ada.adaValueOf 3 <> G.gameTokenVal)

-- Runs 'runGameSuccess', then wallet 2 transfers the token to wallet 1, which takes
-- out another couple of Ada.
runGameSuccess2 :: (EM.MonadEmulator e m) => m ()
runGameSuccess2 = do
    runGameSuccess

    void $ EM.processEmulated $ do
        _ <- EM.runWalletAction w2 (W.payToPublicKey_ W.defaultSlotRange G.gameTokenVal (EM.walletPubKey w1))
        processAndNotify
        _ <- EM.runWalletAction w1 (guess "new secret" "hello" (Ada.adaValueOf 2) (Ada.adaValueOf 3))
        processAndNotify
        EM.assertOwnFundsEq w1 (Ada.adaValueOf 4 <> G.gameTokenVal)

-- Wallet 2 makes a wrong guess and fails to take out the funds
runGameFailure :: (EM.MonadEmulator e m) => m ()
runGameFailure = void $ EM.processEmulated $ do
        processAndNotify
        _   <- EM.runWalletAction w1 G.startGame
        _   <- EM.runWalletAction w2 G.startGame
        processAndNotify
        _ <- EM.runWalletAction w1 (G.lock "hello" (Ada.adaValueOf 8))
        processAndNotify
        processAndNotify
        _ <- EM.runWalletAction w1 (W.payToPublicKey_ W.defaultSlotRange G.gameTokenVal (EM.walletPubKey w2))
        processAndNotify
        _ <- EM.runWalletAction w2 (guess "hola" "new secret" (Ada.adaValueOf 3) (Ada.adaValueOf 5))
        processAndNotify
        EM.assertOwnFundsEq w2 (initialVal <> G.gameTokenVal)
