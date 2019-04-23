{-# LANGUAGE FlexibleContexts #-}
module Spec.Currency(tests) where

import           Control.Monad                                     (void)
import           Control.Monad.Except
import qualified Data.Map                                          as Map
import qualified Data.Text                                         as T
import qualified Spec.Size                                         as Size
import           Test.Tasty
import qualified Test.Tasty.HUnit                                  as HUnit

import           Language.PlutusTx.Coordination.Contracts.Currency (Currency)
import qualified Language.PlutusTx.Coordination.Contracts.Currency as Cur
import qualified Ledger.Ada                                        as Ada
import           Ledger.Value                                      (Value)
import qualified Wallet.Emulator                                   as EM

tests :: TestTree
tests = HUnit.testCaseSteps "forge a simple currency" $ \step -> do
    let initialState = EM.emulatorStateInitialDist (Map.singleton (EM.walletPubKey w1) initialVal)
        (result, st) = EM.runEmulator initialState runForge

    case result of
        Left  err   -> do
            step (show st)
            step (show err)
            HUnit.assertFailure "own funds not equal"
        Right cur ->
            Size.reasonable (Cur.curValidator cur) 50000

initialVal :: Value
initialVal = Ada.adaValueOf 10

w1 :: EM.Wallet
w1 = EM.Wallet 1

runForge :: (EM.MonadEmulator m) => m Currency
runForge = do
    let
        processAndNotify = void (EM.addBlocksAndNotify [w1] 1)
        amounts = [("my currency", 1000), ("my token", 1)]

    (r, _) <- EM.processEmulated $ do
        processAndNotify
        cur <- EM.runWalletAction w1 (Cur.forge amounts)
        processAndNotify
        processAndNotify
        processAndNotify
        processAndNotify
        pure cur

    c <- either (throwError . EM.AssertionError . T.pack . show) pure r
    EM.processEmulated $
        EM.assertOwnFundsEq w1 (initialVal <> Cur.forgedValue c)

    pure c
