{-# LANGUAGE OverloadedStrings #-}
module NonFungible.NonFungible7Spec (spec) where

import           Utils

import           NonFungible.NonFungible7

import           Ledger
import qualified Ledger.Ada                 as A
import qualified Ledger.Value               as V
import           Wallet.Emulator

import           Control.Monad              (void)
import qualified Data.ByteString.Lazy.Char8 as C
import           Data.Either                (isRight)
import           Data.Text                  (Text)
import           Test.Hspec

{-# ANN spec ("HLint: ignore Reduce duplication" :: Text) #-}
spec :: Spec
spec =
    describe "start/forge" $
        it "can forge the same token twice" $
            fst (getResult tr) `shouldSatisfy` isRight
  where
    monaLisa, starryNight :: String
    monaLisa = "Mona Lisa"
    starryNight = "The Starry Night"

    tr :: Trace MockWallet ()
    tr = void $ do
        updateWallets
        void $ walletAction w1 start
        updateWallets
        void $ walletAction w1 $ forge starryNight
        updateWallets
        void $ walletAction w1 $ forge monaLisa
        updateWallets
        void $ walletAction w1 start
        updateWallets
        void $ walletAction w1 $ forge monaLisa
        updateWallets
        assertOwnFundsEq w1 $
               A.toValue initialAda
            <> tokenValue monaLisa
            <> tokenValue monaLisa
            <> tokenValue starryNight

symbol :: CurrencySymbol
symbol = nonFungibleSymbol $ NonFungible {issuer = key1}

tokenValue :: String -> Value
tokenValue name = V.singleton symbol (V.TokenName $ C.pack name) 1
