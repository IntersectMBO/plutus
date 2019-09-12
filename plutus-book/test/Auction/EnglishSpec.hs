{-# LANGUAGE OverloadedStrings #-}
module Auction.EnglishSpec (spec) where

import           Utils

import           Auction.English

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
spec = do
    describe "auction" $ do
        it "works for a normal auction" $
            fst (getResult tr1) `shouldSatisfy` isRight
        it "works for an auction without bids" $ do
            fst (getResult tr2) `shouldSatisfy` isRight
        it "does not allow reclaiming the token if there was a bid" $
            fst (getResult tr3) `shouldSatisfy` isRight
    describe "runAuction" $ do
        it "works for a successful auction" $
            fst (getResult tr4) `shouldSatisfy` isRight
        it "works for a failed auction" $
            fst (getResult tr5) `shouldSatisfy` isRight
    describe "autoBid" $ do
        it "runs a successful auction" $
            fst (getResult tr6) `shouldSatisfy` isRight
  where
    guernica :: String
    guernica = "Guernica"

    bid1, bid2, bid3 :: Ada
    bid1 = 10000
    bid2 = 11000
    bid3 = 12000

    tokenName :: String -> V.TokenName
    tokenName = V.TokenName . C.pack

    trStart :: Trace MockWallet (CurrencySymbol, V.TokenName, Value)
    trStart = do
        updateWallets
        (adSymbol, _) <- runSuccessfulWalletAction w1 start'
        let nfSymbol :: CurrencySymbol
            nfSymbol = nonFungibleSymbol $ NonFungible
                { issuer        = key1
                , adminCurrency = adSymbol
                }

            tokenValue' :: String -> Value
            tokenValue' name = V.singleton nfSymbol (tokenName name) 1

        replicateM_ 5 updateWallets
        void $ walletAction w1 $ forge adSymbol guernica
        updateWallets
        assertOwnFundsEq w1 $
               A.toValue initialAda
            <> tokenValue' guernica

        return (nfSymbol, tokenName guernica, tokenValue' guernica)

    tr1 :: Trace MockWallet ()
    tr1 = void $ do
        (nfSymbol, tname, tvalue) <- trStart
        let ea = EnglishAuction
                    { eaSymbol = nfSymbol
                    , eaName   = tname
                    , eaOwner  = key1
                    , eaMinBid = 10000
                    , eaMinInc = 1000
                    , eaEndBid = Slot 20
                    , eaFinish = Slot 30
                    }
        void $ walletAction w2 $ watchAuction ea
        void $ walletAction w3 $ watchAuction ea
        updateWallets
        void $ walletAction w1 $ startAuction
            (eaSymbol ea)
            (eaName ea)
            (eaMinBid ea)
            (eaMinInc ea)
            (eaEndBid ea)
            (eaFinish ea)
        updateWallets
        assertOwnFundsEq w1 $ A.toValue initialAda

        void $ walletAction w2 $ bid ea bid1
        updateWallets
        assertOwnFundsEq w2 $ A.toValue $ initialAda - bid1

        void $ walletAction w3 $ bid ea bid2
        updateWallets
        assertOwnFundsEq w3 $ A.toValue $ initialAda - bid2

        void $ walletAction w2 $ reclaimBid ea bid1
        updateWallets
        assertOwnFundsEq w2 $ A.toValue initialAda

        void $ walletAction w2 $ bid ea bid3
        updateWallets
        assertOwnFundsEq w2 $ A.toValue $ initialAda - bid3

        void $ walletAction w3 $ reclaimBid ea bid2
        updateWallets
        assertOwnFundsEq w3 $ A.toValue initialAda

        void $ walletAction w1 $ claimBid
            (eaSymbol ea)
            (eaName ea)
            (eaMinBid ea)
            (eaMinInc ea)
            (eaEndBid ea)
            (eaFinish ea)
            bid3
        replicateM_ 10 updateWallets

        void $ walletAction w2 $ claimToken ea
        replicateM_ 10 updateWallets

        assertOwnFundsEq w1 $ A.toValue $ initialAda + bid3
        assertOwnFundsEq w2 $ A.toValue (initialAda - bid3) <> tvalue
        assertOwnFundsEq w3 $ A.toValue initialAda

    tr2 :: Trace MockWallet ()
    tr2 = void $ do
        (nfSymbol, tname, tvalue) <- trStart
        let ea = EnglishAuction
                    { eaSymbol = nfSymbol
                    , eaName   = tname
                    , eaOwner  = key1
                    , eaMinBid = 10000
                    , eaMinInc = 1000
                    , eaEndBid = Slot 20
                    , eaFinish = Slot 30
                    }
        void $ walletAction w1 $ startAuction
            (eaSymbol ea)
            (eaName ea)
            (eaMinBid ea)
            (eaMinInc ea)
            (eaEndBid ea)
            (eaFinish ea)
        updateWallets

        void $ walletAction w1 $ reclaimToken
            (eaSymbol ea)
            (eaName ea)
            (eaMinBid ea)
            (eaMinInc ea)
            (eaEndBid ea)
            (eaFinish ea)
        replicateM_ 13 updateWallets
        assertOwnFundsEq w1 $ A.toValue initialAda <> tvalue

    tr3 :: Trace MockWallet ()
    tr3 = void $ do
        (nfSymbol, tname, _) <- trStart
        let ea = EnglishAuction
                    { eaSymbol = nfSymbol
                    , eaName   = tname
                    , eaOwner  = key1
                    , eaMinBid = 10000
                    , eaMinInc = 1000
                    , eaEndBid = Slot 20
                    , eaFinish = Slot 30
                    }
        void $ walletAction w2 $ watchAuction ea
        updateWallets
        void $ walletAction w1 $ startAuction
            (eaSymbol ea)
            (eaName ea)
            (eaMinBid ea)
            (eaMinInc ea)
            (eaEndBid ea)
            (eaFinish ea)
        updateWallets

        void $ walletAction w2 $ bid ea bid1
        updateWallets

        void $ walletAction w1 $ reclaimToken
            (eaSymbol ea)
            (eaName ea)
            (eaMinBid ea)
            (eaMinInc ea)
            (eaEndBid ea)
            (eaFinish ea)
        replicateM_ 11 updateWallets
        assertOwnFundsEq w1 $ A.toValue initialAda

    tr4 :: Trace MockWallet ()
    tr4 = void $ do
        (nfSymbol, tname, tvalue) <- trStart
        let ea = EnglishAuction
                    { eaSymbol = nfSymbol
                    , eaName   = tname
                    , eaOwner  = key1
                    , eaMinBid = 10000
                    , eaMinInc = 1000
                    , eaEndBid = Slot 20
                    , eaFinish = Slot 30
                    }
        void $ walletAction w2 $ watchAuction ea
        void $ walletAction w3 $ watchAuction ea
        updateWallets
        void $ walletAction w1 $ runAuction
            (eaSymbol ea)
            (eaName ea)
            (eaMinBid ea)
            (eaMinInc ea)
            (eaEndBid ea)
            (eaFinish ea)
        updateWallets

        void $ walletAction w2 $ bid ea bid1
        updateWallets

        void $ walletAction w3 $ bid ea bid2
        updateWallets

        void $ walletAction w2 $ reclaimBid ea bid1
        updateWallets

        void $ walletAction w2 $ bid ea bid3
        updateWallets

        void $ walletAction w3 $ reclaimBid ea bid2

        replicateM_ 10 updateWallets

        void $ walletAction w2 $ claimToken ea
        replicateM_ 10 updateWallets

        assertOwnFundsEq w1 $ A.toValue $ initialAda + bid3
        assertOwnFundsEq w2 $ A.toValue (initialAda - bid3) <> tvalue
        assertOwnFundsEq w3 $ A.toValue initialAda

    tr5 :: Trace MockWallet ()
    tr5 = void $ do
        (nfSymbol, tname, tvalue) <- trStart
        let ea = EnglishAuction
                    { eaSymbol = nfSymbol
                    , eaName   = tname
                    , eaOwner  = key1
                    , eaMinBid = 10000
                    , eaMinInc = 1000
                    , eaEndBid = Slot 20
                    , eaFinish = Slot 30
                    }
        void $ walletAction w1 $ runAuction
            (eaSymbol ea)
            (eaName ea)
            (eaMinBid ea)
            (eaMinInc ea)
            (eaEndBid ea)
            (eaFinish ea)

        replicateM_ 14 updateWallets

        assertOwnFundsEq w1 $ A.toValue initialAda <> tvalue

    tr6 :: Trace MockWallet ()
    tr6 = void $ do
        (nfSymbol, tname, tvalue) <- trStart
        let ea = EnglishAuction
                    { eaSymbol = nfSymbol
                    , eaName   = tname
                    , eaOwner  = key1
                    , eaMinBid = 10000
                    , eaMinInc = 1000
                    , eaEndBid = Slot 20
                    , eaFinish = Slot 30
                    }
        void $ walletAction w2 $ autoBid ea 14444
        void $ walletAction w3 $ autoBid ea 15555
        void $ walletAction w4 $ autoBid ea 12222
        updateWallets

        void $ walletAction w1 $ runAuction
            (eaSymbol ea)
            (eaName ea)
            (eaMinBid ea)
            (eaMinInc ea)
            (eaEndBid ea)
            (eaFinish ea)

        replicateM_ 25 updateWallets

        let highest = 15000
        assertOwnFundsEq w1 $ A.toValue $ initialAda + highest
        assertOwnFundsEq w2 $ A.toValue initialAda
        assertOwnFundsEq w3 $ A.toValue (initialAda - highest) <> tvalue
        assertOwnFundsEq w4 $ A.toValue initialAda
