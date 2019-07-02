module OffChain.PayToWalletSpec (spec) where

import           Utils

import qualified OffChain.PayToWallet       as P1
import qualified OffChain.PayToWalletSimple as P2

import           Ledger
import           Ledger.Ada
import           Wallet.Emulator

import           Control.Monad              (void)
import           Data.Either                (isRight)
import           Test.Hspec

spec :: Spec
spec = do
    describe "payToWallet (version 1)" $ mkSpec P1.myPayToWallet
    describe "payToWallet (version 2)" $ mkSpec P2.myPayToWallet

mkSpec :: (Wallet -> Ada -> MockWallet ()) -> SpecWith ()
mkSpec payToWallet =
    it "transfers funds as expected" $
        isRight (fst $ getResult tr) `shouldBe` True
  where
    ada :: Ada
    ada = fromInt 8

    tr :: Trace MockWallet ()
    tr = void $ do
        updateWallets
        void $ walletAction w1 $ payToWallet w2 ada
        updateWallets
        assertFunds (initialAda `minus` ada) (initialAda `plus` ada)
