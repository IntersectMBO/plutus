{-# LANGUAGE FlexibleContexts #-}
module Spec.Currency(tests) where

import           Control.Monad                                     (void, when)
import           Control.Monad.Except
import           Data.Either                                       (isLeft, isRight)
import qualified Data.Map                                          as Map
import qualified Data.Text                                         as T
import           Test.Tasty
import qualified Test.Tasty.HUnit                                  as HUnit

import qualified Language.PlutusTx.Coordination.Contracts.Currency as Cur
import qualified Ledger.Ada                                        as Ada
import           Ledger.Value                                      (Value)
import qualified Wallet.Emulator                                   as EM

tests :: TestTree
tests = HUnit.testCaseSteps "forge a simple currency" $ \step -> do
    let initialState = EM.emulatorStateInitialDist (Map.singleton (EM.walletPubKey w1) initialVal)
        (result, st) = EM.runEmulator initialState runForge

    when (isLeft result) $ step (show st)

    HUnit.assertBool "own funds not equal" (isRight result)

initialVal :: Value
initialVal = Ada.adaValueOf 10

w1 :: EM.Wallet
w1 = EM.Wallet 1

runForge :: (EM.MonadEmulator m) => m ()
runForge = do
    let
        processAndNotify = void (EM.addBlocksAndNotify [w1] 1)
        amount = 1000 -- how much of the currency to forge
        currencyName = "my token"

    (r, _) <- EM.processEmulated $ do
        processAndNotify
        cur <- EM.runWalletAction w1 (Cur.forge currencyName amount)
        processAndNotify
        processAndNotify
        processAndNotify
        processAndNotify
        pure cur

    c <- either (throwError . EM.AssertionError . T.pack . show) pure r
    EM.processEmulated $
        EM.assertOwnFundsEq w1 (initialVal <> Cur.forgedValue c)
