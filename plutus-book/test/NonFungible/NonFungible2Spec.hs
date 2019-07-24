{-# LANGUAGE OverloadedStrings #-}
module NonFungible.NonFungible2Spec (spec) where

import           Utils

import           NonFungible.NonFungible2

import           Ledger
import qualified Ledger.Ada                 as A
import qualified Ledger.Value               as V
import           Wallet.Emulator

import           Control.Monad              (void)
import qualified Data.ByteString.Lazy.Char8 as C
import           Data.Either                (isRight)
import           Test.Hspec

spec :: Spec
spec =
    describe "prank" $
        it "pranks" $
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
        void $ walletAction w1 $ forge monaLisa
        updateWallets
        void $ walletAction w2 $ prank $ Wallet 1
        updateWallets
        void $ walletAction w1 $ forge starryNight
        updateWallets
        assertOwnFundsEq w1 $
               A.toValue initialAda
            <> tokenValue monaLisa
        assertOwnFundsEq w2 $ A.toValue initialAda

symbol :: CurrencySymbol
symbol = nonFungibleSymbol $ NonFungible {issuer = key1}

tokenValue :: String -> Value
tokenValue name = V.singleton symbol (V.TokenName $ C.pack name) 1
