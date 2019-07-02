module OffChain.PayToWalletSpec (spec) where

import           Utils

import qualified OffChain.PayToWallet       as P1
import qualified OffChain.PayToWalletSimple as P2

import           Ledger
import           Ledger.Ada
import           Wallet.Emulator
import           Wallet.Emulator.Generators

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
        isRight (fst res) `shouldBe` True
  where
    ada :: Ada
    ada = fromInt 8

    tr :: Trace MockWallet ()
    tr = void $ do
        updateWallets
        void $ walletAction w1 $ payToWallet w2 ada
        updateWallets
        assertOwnFundsEq w1 $ toValue $ initialAda `minus` ada
        assertOwnFundsEq w2 $ toValue $ initialAda `plus` ada

    res :: (Either AssertionError (), EmulatorState)
    res = runTrace initialChain tr
