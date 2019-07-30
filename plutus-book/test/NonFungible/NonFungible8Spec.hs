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

{-# ANN spec ("HLint: ignore" :: Text) #-}

spec :: Spec
spec =
    describe "start/forge" $
        it "forges and prevents forging the same token twice" $
            fst (getResult tr) `shouldSatisfy` isRight
  where
    monaLisa, starryNight :: String
    monaLisa = "Mona Lisa"
    starryNight = "The Starry Night"


    tr :: Trace MockWallet ()
    tr = void $ do
        updateWallets
        (maybeAdSymbol, _) <- runWalletAction w1 start
        let adSymbol :: CurrencySymbol
            adSymbol = case maybeAdSymbol of
                Right s -> s
                Left _  -> error "Error creating admin symbol"
            nfSymbol :: CurrencySymbol
            nfSymbol = nonFungibleSymbol $ NonFungible
                { issuer        = key1
                , adminCurrency = adSymbol
                }
            tokenValue :: String -> Value
            tokenValue name = V.singleton nfSymbol (V.TokenName $ C.pack name) 1
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
