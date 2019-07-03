{-# LANGUAGE OverloadedStrings #-}

module OffChain.HelloSpec (spec) where

import           Utils

import           OffChain.Hello  (hello)

import           Wallet.Emulator

import           Control.Monad   (void)
import           Data.Either     (isRight)
import           Test.Hspec

spec :: Spec
spec = describe "hello" $
    it "logs the expected message" $ do
        let res = getResult tr
        isRight (fst res) `shouldBe` True
        _emulatorLog (snd res) `shouldBe` [WalletInfo w "Hello from the wallet!"]
  where
    w :: Wallet
    w = Wallet 1

    tr :: Trace MockWallet ()
    tr = void $ walletAction w hello
