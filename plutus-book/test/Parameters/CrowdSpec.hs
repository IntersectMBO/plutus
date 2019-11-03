{-# LANGUAGE OverloadedStrings #-}
module Parameters.CrowdSpec (spec) where

import           Utils

import           Parameters.Crowd

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
spec = describe "crowd" $ do
    it "works for a successful campaign" $
        fst (getResult tr1) `shouldSatisfy` isRight
    it "works for a failed campaign" $
        fst (getResult tr2) `shouldSatisfy` isRight
  where
    ft, ada2, ada3 :: Ada
    ft   = lovelaceOf 10000
    ada2 = lovelaceOf  4000
    ada3 = lovelaceOf  7000

    ed, cd :: Slot
    ed = Slot 10
    cd = Slot 20

    campaign :: Campaign
    campaign = Campaign
        { campaignOwner      = key1
        , fundingTarget      = ft
        , endDate            = ed
        , collectionDeadline = cd
        }

    tr1, tr2 :: Trace MockWallet ()
    tr1 = void $ do
        updateWallets
        void $ walletAction w1 $ startCampaign ft ed cd
        updateWallets
        void $ walletAction w2 $ contribute campaign ada2
        updateWallets
        void $ walletAction w3 $ contribute campaign ada3
        updateWallets
        assertFunds3
            initialAda
            (initialAda P.- ada2)
            (initialAda P.- ada3)
        replicateM_ 7 updateWallets
        assertFunds3
            (initialAda P.+ ada2 P.+ ada3)
            (initialAda P.- ada2)
            (initialAda P.- ada3)

    tr2 = void $ do
        updateWallets
        void $ walletAction w1 $ startCampaign ft ed cd
        updateWallets
        void $ walletAction w2 $ contribute campaign ada2
        updateWallets
        assertFunds2 initialAda (initialAda P.- ada2)
        replicateM_ 18 updateWallets
        assertFunds2 initialAda initialAda
