{-# LANGUAGE FlexibleContexts #-}
module Spec.GameStateMachine(tests) where

import           Control.Monad                                             (void)
import qualified Data.Map                                                  as Map
import qualified Spec.Size                                                 as Size
import           Test.Tasty
import qualified Test.Tasty.HUnit                                          as HUnit

import           Language.PlutusTx.Coordination.Contracts.GameStateMachine as G
import qualified Ledger.Ada                                                as Ada
import           Ledger.Value                                              (Value)
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
                    Size.reasonable G.gameValidator 55000
    in
        testGroup "state machine tests" [
            HUnit.testCaseSteps "run a successful game trace"
                (checkResult (EM.runEmulator initialState runGameSuccess)),
            HUnit.testCaseSteps "run a 2nd successful game trace"
                (checkResult (EM.runEmulator initialState runGameSuccess2)),
            HUnit.testCaseSteps "run a failed trace"
                (checkResult (EM.runEmulator initialState runGameFailure))
        ]

initialVal :: Value
initialVal = Ada.adaValueOf 10

w1 :: EM.Wallet
w1 = EM.Wallet 1

w2 :: EM.Wallet
w2 = EM.Wallet 2

w3 :: EM.Wallet
w3 = EM.Wallet 3

processAndNotify :: W.WalletAPI m => EM.Trace m ()
processAndNotify = void (EM.addBlocksAndNotify [w1, w2, w3] 1)

-- Wallet 1 locks some funds using the secret "hello". Then wallet 1
-- transfers the token to wallet 2, and wallet 2 makes a correct guess
-- and locks the remaining funds using the secret "new secret".
runGameSuccess :: (EM.MonadEmulator m) => m ()
runGameSuccess = void $ EM.processEmulated $ do
        processAndNotify
        _   <- EM.runWalletAction w1 G.startGame
        _   <- EM.runWalletAction w2 G.startGame
        processAndNotify
        _ <- EM.runWalletAction w1 (G.lock "hello" 8)
        processAndNotify
        processAndNotify
        _ <- EM.runWalletAction w1 (W.payToPublicKey_ W.defaultSlotRange G.gameTokenVal (EM.walletPubKey w2))
        processAndNotify
        _ <- EM.runWalletAction w2 (guess "hello" "new secret" 3 5)
        processAndNotify
        EM.assertOwnFundsEq w2 (initialVal <> Ada.adaValueOf 3 <> G.gameTokenVal)

-- Runs 'runGameSuccess', then wallet 2 transfers the token to wallet 1, which takes
-- out another couple of Ada.
runGameSuccess2 :: (EM.MonadEmulator m) => m ()
runGameSuccess2 = do
    runGameSuccess

    void $ EM.processEmulated $ do
        _ <- EM.runWalletAction w2 (W.payToPublicKey_ W.defaultSlotRange G.gameTokenVal (EM.walletPubKey w1))
        processAndNotify
        _ <- EM.runWalletAction w1 (guess "new secret" "hello" 2 3)
        processAndNotify
        EM.assertOwnFundsEq w1 (Ada.adaValueOf 4 <> G.gameTokenVal)

-- Wallet 2 makes a wrong guess and fails to take out the funds
runGameFailure :: (EM.MonadEmulator m) => m ()
runGameFailure = void $ EM.processEmulated $ do
        processAndNotify
        _   <- EM.runWalletAction w1 G.startGame
        _   <- EM.runWalletAction w2 G.startGame
        processAndNotify
        _ <- EM.runWalletAction w1 (G.lock "hello" 8)
        processAndNotify
        processAndNotify
        _ <- EM.runWalletAction w1 (W.payToPublicKey_ W.defaultSlotRange G.gameTokenVal (EM.walletPubKey w2))
        processAndNotify
        _ <- EM.runWalletAction w2 (guess "hola" "new secret" 3 5)
        processAndNotify
        EM.assertOwnFundsEq w2 (initialVal <> G.gameTokenVal)

