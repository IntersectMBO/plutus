{-# LANGUAGE OverloadedStrings #-}
module Multi.VestingSpec (spec) where

import           Utils

import           Multi.Vesting

import qualified Language.PlutusTx.Numeric as P
import           Ledger
import           Ledger.Ada
import           Wallet.Emulator

import           Control.Monad             (replicateM_, void)
import           Data.Either               (isRight)
import           Data.Text                 (Text)
import           Test.Hspec

{-# ANN spec ("HLint: ignore Reduce duplication" :: Text) #-}
spec :: Spec
spec = describe "vesting" $ do
    it "works for legal withdrawels" $
        fst (getResult $ tr 8 9 $ ada1 P.+ ada2) `shouldSatisfy` isRight
    it "works for too early withdrawels" $
        fst (getResult $ tr 8 7 ada1) `shouldSatisfy` isRight
  where
    ada1, ada2 :: Ada
    ada1 = lovelaceOf  4000
    ada2 = lovelaceOf  6000

    s1, s2 :: Slot
    s1 = Slot 10
    s2 = Slot 20

    t1, t2 :: Tranche
    t1 = Tranche
        { amount = ada1
        , date   = s1
        }
    t2 = Tranche
        { amount = ada2
        , date   = s2
        }

    v :: Vesting
    v = Vesting
        { tranche1 = t1
        , tranche2 = t2
        , owner    = key2
        }

    tr :: Int -> Int -> Ada -> Trace MockWallet ()
    tr d1 d2 ada = void $ do
        updateWallets
        void $ walletAction w2 $ registerScheme t1 t2
        updateWallets
        void $ walletAction w1 $ vest v
        replicateM_ d1 updateWallets
        void $ walletAction w2 $ withdraw t1 t2 $ lovelaceOf 2000
        updateWallets
        void $ walletAction w2 $ withdraw t1 t2 $ lovelaceOf 2000
        replicateM_ d2 updateWallets
        void $ walletAction w2 $ withdraw t1 t2 $ lovelaceOf 5000
        updateWallets
        void $ walletAction w2 $ withdraw t1 t2 $ lovelaceOf 1000
        updateWallets
        assertFunds2
            (initialAda P.- (ada1 P.+ ada2))
            (initialAda P.+ ada)
