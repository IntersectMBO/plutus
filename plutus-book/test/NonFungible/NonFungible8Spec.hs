{-# LANGUAGE OverloadedStrings #-}
module NonFungible.NonFungible8Spec (spec) where

import           Utils

import           NonFungible.NonFungible8

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
spec =
    describe "start/forge" $
        it "forges and prevents forging the same token twice" $
            fst (getResult tr) `shouldSatisfy` isRight
  where
    monaLisa, starryNight :: String
    monaLisa = "Mona Lisa"
    starryNight = "The Starry Night"

    adSymbol :: CurrencySymbol
    adSymbol = "2c7c99a4f09e98aae7b8d213814ffa60b9b737adaef1ba244cde0a04a7e8e128"

    nfSymbol :: CurrencySymbol
    nfSymbol = nonFungibleSymbol $ NonFungible
        { issuer        = key1
        , adminCurrency = adSymbol
        }

    tokenValue :: String -> Value
    tokenValue name = V.singleton nfSymbol (V.TokenName $ C.pack name) 1

    tr :: Trace MockWallet ()
    tr = void $ do
        updateWallets
        void $ walletAction w1 start
        replicateM_ 5 updateWallets
        void $ walletAction w1 $ forge adSymbol monaLisa
        updateWallets
        void $ walletAction w1 $ forge adSymbol starryNight
        updateWallets
        void $ walletAction w1 $ forge adSymbol monaLisa
        updateWallets
        assertOwnFundsEq w1 $
               A.toValue initialAda
            <> tokenValue monaLisa
            <> tokenValue starryNight
