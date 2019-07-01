{-# LANGUAGE OverloadedStrings #-}

module Spec.PayToWalletSpec (spec) where

import qualified PayToWallet1               as P1
import qualified PayToWallet2               as P2

import           Ledger
import           Ledger.Ada
import           Wallet.Emulator
import           Wallet.Emulator.Generators
import           Wallet.Generators

import           Control.Arrow              (first)
import           Control.Monad              (void)
import           Data.Either                (isRight)
import qualified Data.Map.Strict            as Map
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
    w1, w2 :: Wallet
    w1 = Wallet 1
    w2 = Wallet 2

    adaInit, ada :: Ada
    adaInit = fromInt 100000
    ada     = fromInt 8

    update :: Trace MockWallet ()
    update = void $ processPending >>= walletsNotifyBlock [w1, w2]

    tr :: Trace MockWallet ()
    tr = void $ do
        update
        void $ walletAction w1 $ payToWallet w2 ada
        update
        assertOwnFundsEq w1 $ toValue $ adaInit `minus` ada
        assertOwnFundsEq w2 $ toValue $ adaInit `plus` ada

    chain :: Mockchain
    chain =
        let (txn, ot) = genInitialTransaction generatorModel
            txId      = hashTx txn
        in  Mockchain {
                mockchainInitialBlock = [txn],
                mockchainUtxo = Map.fromList $ first (TxOutRefOf txId) <$> zip [0..] ot
            }

    res :: (Either AssertionError (), EmulatorState)
    res = runTrace chain tr
