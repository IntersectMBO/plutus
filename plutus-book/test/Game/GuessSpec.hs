module Game.GuessSpec (spec) where

import           Utils

import           Game.Guess

import           Ledger
import           Ledger.Ada
import           Wallet.Emulator

import           Control.Monad   (void)
import           Data.Either     (isRight)
import           Test.Hspec

spec :: Spec
spec = describe "guess" $ do
    it "works for a correct guess" $
        isRight (fst $ getResult tr1) `shouldBe` True
    it "works for an incorrect guess" $
        isRight (fst $ getResult tr2) `shouldBe` True
  where
    ada :: Ada
    ada = fromInt 10000

    tr1, tr2 :: Trace MockWallet ()
    tr1 = void $ do
        updateWallets
        void $ walletAction w2 startGame
        updateWallets
        void $ walletAction w1 $ lock "Haskell" ada
        updateWallets
        void $ walletAction w2 $ guess "Haskell"
        updateWallets
        assertFunds (initialAda - ada) (initialAda + ada)
    tr2 = void $ do
        updateWallets
        void $ walletAction w2 startGame
        updateWallets
        void $ walletAction w1 $ lock "Haskell" ada
        updateWallets
        void $ walletAction w2 $ guess "Scala"
        updateWallets
        assertFunds (initialAda - ada) initialAda
