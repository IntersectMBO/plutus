module Spec.TriggerSpec (spec) where

import           Utils

import qualified Trigger                    as T1
import qualified TriggerSimple              as T2

import           Ledger
import           Ledger.Ada
import           Wallet.Emulator
import           Wallet.Emulator.Generators

import           Control.Monad              (void)
import           Data.Either                (isRight)
import           Test.Hspec

spec :: Spec
spec = do
    describe "waitUntil (version 1)" $ mkSpec T1.waitUntil
    describe "waitUntil (version 2)" $ mkSpec T2.waitUntil

mkSpec :: (Slot -> Wallet -> Ada -> MockWallet ()) -> SpecWith ()
mkSpec waitUntil =
    it "behaves as expected" $
        isRight (fst res) `shouldBe` True

  where
    ada :: Ada
    ada = fromInt 10000

    tr :: Trace MockWallet ()
    tr = void $ do
        updateWallets
        void $ walletAction w1 $ waitUntil (Slot 5) w2 ada
        updateWallets
        updateWallets
        updateWallets
        updateWallets
        assertFunds initialAda initialAda
        updateWallets
        assertFunds (initialAda `minus` ada) (initialAda `plus` ada)

    assertFunds :: Ada -> Ada -> Trace MockWallet ()
    assertFunds ada1 ada2 = do
        assertOwnFundsEq w1 $ toValue $ ada1
        assertOwnFundsEq w2 $ toValue $ ada2

    res :: (Either AssertionError (), EmulatorState)
    res = runTrace initialChain tr
