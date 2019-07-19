{-# LANGUAGE OverloadedStrings #-}
module Token.FungibleSpec (spec) where

import           Utils

import           Token.Fungible

import           Ledger
import qualified Ledger.Ada                 as A
import qualified Ledger.Value               as V
import           Wallet.Emulator

import           Control.Monad              (replicateM_, void)
import qualified Data.ByteString.Lazy.Char8 as C
import           Data.Either                (isRight)
import           Data.Text                  (Text)
import           Test.Hspec

{-# ANN spec ("HLint: ignore Reduce duplication" :: Text) #-}
spec :: Spec
spec = do
    describe "forge" $
        it "forges" $
            fst (getResult tr1) `shouldSatisfy` isRight
    describe "buy/sell" $ do
        it "works if both parties pay" $
            fst (getResult tr2) `shouldSatisfy` isRight
        it "works if buyer doesn't pay" $
            fst (getResult tr3) `shouldSatisfy` isRight
        it "works if seller doesn't pay" $
            fst (getResult tr4) `shouldSatisfy` isRight
  where
    plutus :: String
    plutus = "Plutus"

    p1, p2 :: Integer
    p1 = 200000
    p2 = 100000

    ada :: Ada
    ada = A.fromInt 50000

    price :: Value
    price = A.toValue ada

    sl :: Slot
    sl = Slot 15

    tr1, tr2, tr3, tr4 :: Trace MockWallet ()
    tr1 = void $ do
        updateWallets
        void $ walletAction w1 $ forge plutus p1
        updateWallets
        updateWallets
        assertOwnFundsEq w1 $ A.toValue initialAda <> plutusValue p1
    tr2 = void $ do
        updateWallets
        void $ walletAction w1 $ forge plutus p1
        updateWallets
        updateWallets
        void $ walletAction w1 sell'
        void $ walletAction w2 buy'
        updateWallets
        updateWallets
        assertOwnFundsEq w1 $
            (A.toValue initialAda <> plutusValue p1 <> price)
                `V.minus` plutusValue p2
        assertOwnFundsEq w2 $
            (A.toValue initialAda <> plutusValue p2)
                `V.minus` price
    tr3 = void $ do
        updateWallets
        void $ walletAction w1 $ forge plutus p1
        updateWallets
        updateWallets
        void $ walletAction w1 sell'
        replicateM_ 13 updateWallets
        assertOwnFundsEq w1 $ A.toValue initialAda <> plutusValue p1
        assertOwnFundsEq w2 $ A.toValue initialAda
    tr4 = void $ do
        updateWallets
        void $ walletAction w1 $ forge plutus p1
        updateWallets
        updateWallets
        void $ walletAction w2 buy'
        replicateM_ 13 updateWallets
        assertOwnFundsEq w1 $ A.toValue initialAda <> plutusValue p1
        assertOwnFundsEq w2 $ A.toValue initialAda

    sell', buy' :: MockWallet ()
    sell' = sell
        key1
        plutus
        p2
        price
        key2
        sl
    buy' = buy
        key1
        plutus
        p2
        key1
        price
        sl


plutusName :: String
plutusName = "Plutus"

plutusFungible :: Fungible
plutusFungible = Fungible
    { name   = V.TokenName $ C.pack plutusName
    , issuer = key1
    }

plutusValue :: Integer -> Value
plutusValue = fungibleValue plutusFungible
