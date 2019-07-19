module OffChain.TriggerSpec (spec) where

import           Utils

import qualified OffChain.Trigger       as T1
import qualified OffChain.TriggerSimple as T2

import           Ledger
import           Ledger.Ada
import           Wallet.Emulator

import           Control.Monad          (void)
import           Data.Either            (isRight)
import           Test.Hspec

spec :: Spec
spec = do
    describe "waitUntil (version 1)" $ mkSpec T1.waitUntil
    describe "waitUntil (version 2)" $ mkSpec T2.waitUntil

mkSpec :: (Slot -> Wallet -> Ada -> MockWallet ()) -> SpecWith ()
mkSpec waitUntil =
    it "behaves as expected" $
        fst (getResult tr) `shouldSatisfy` isRight

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
        assertFunds2 initialAda initialAda
        updateWallets
        assertFunds2 (initialAda `minus` ada) (initialAda `plus` ada)
