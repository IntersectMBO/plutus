{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE GADTs             #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications  #-}

module Spec.Stablecoin(
    tests
    ) where


import           Control.Monad                                       (void)
import           Language.Plutus.Contract.Test
import           Language.PlutusTx.Numeric                           (negate, one, zero)
import           Language.PlutusTx.Ratio                             as Ratio
import           Ledger.Ada                                          (adaSymbol, adaToken)
import qualified Ledger.Ada                                          as Ada
import           Ledger.Address                                      (Address)
import           Ledger.Oracle                                       (Observation, SignedMessage, signObservation)
import           Ledger.Slot                                         (Slot (..))
import           Ledger.Typed.Scripts                                (scriptAddress)
import           Ledger.Value

import           Prelude                                             hiding (negate)
import           Test.Tasty

import           Language.PlutusTx.Coordination.Contracts.Stablecoin (BC (..), ConversionRate, Input (..), RC (..),
                                                                      SC (..), SCAction (..), Stablecoin (..))
import qualified Language.PlutusTx.Coordination.Contracts.Stablecoin as Stablecoin
import qualified Plutus.Trace.Emulator                               as Trace

user :: Wallet
user = Wallet 1

oracle :: Wallet
oracle = Wallet 2

onePercent :: Ratio Integer
onePercent = 1 % 100

coin :: Stablecoin
coin = Stablecoin
    { scOracle = walletPubKey oracle
    , scFee = onePercent
    , scMinReserveRatio = zero
    , scReservecoinDefaultPrice = BC 1
    , scBaseCurrency = (adaSymbol, adaToken)
    , scStablecoinTokenName = "stablecoin"
    , scReservecoinTokenName = "reservecoin"
    }

signConversionRate :: ConversionRate -> SignedMessage (Observation ConversionRate)
signConversionRate rate = signObservation (Slot 0) rate (walletPrivKey oracle)

stablecoinAddress :: Address
stablecoinAddress = scriptAddress $ Stablecoin.scriptInstance coin

initialDeposit :: Value
initialDeposit = Ada.lovelaceValueOf 100

initialFee :: Value
initialFee = Ada.lovelaceValueOf 1

tests :: TestTree
tests = testGroup "Stablecoin"
    [ checkPredicate "mint reservecoins"
        (valueAtAddress stablecoinAddress (== (initialDeposit <> initialFee))
        .&&. assertNoFailedTransactions
        .&&. walletFundsChange user (Stablecoin.reserveCoins coin 100 <> negate (initialDeposit <> initialFee))
        )
        $ initialise >>= mintReserveCoins (RC 100) one

    , checkPredicate "mint reservecoins and stablecoins"
        (valueAtAddress stablecoinAddress (== (initialDeposit <> initialFee <> Ada.lovelaceValueOf 50))
        .&&. assertNoFailedTransactions
        .&&. walletFundsChange user (Stablecoin.stableCoins coin 50 <> Stablecoin.reserveCoins coin 100 <> negate (initialDeposit <> initialFee <> Ada.lovelaceValueOf 50))
        )
        $ do
            hdl <- initialise
            mintReserveCoins (RC 100) one hdl
            -- Mint 50 stablecoins at a rate of 1 Ada: 1 USD
            void $ mintStableCoins (SC 50) one hdl

    , checkPredicate "mint reservecoins, stablecoins and redeem stablecoin at a different price"
        (valueAtAddress stablecoinAddress (== (initialDeposit <> initialFee <> Ada.lovelaceValueOf 30))
        .&&. assertNoFailedTransactions
        .&&. walletFundsChange user (Stablecoin.stableCoins coin 40 <> Stablecoin.reserveCoins coin 100 <> negate (initialDeposit <> initialFee <> Ada.lovelaceValueOf 30))
        )
        $ do
            hdl <- initialise
            mintReserveCoins (RC 100) one hdl
            mintStableCoins (SC 50) one hdl
            -- redeem 10 stablecoins at an exchange rate of 2 Ada : 1 USD (so we get 20 lovelace from the bank)
            redeemStableCoins (SC 10) (Ratio.fromInteger 2) hdl
    ] where
        initialise = do
            hdl <- Trace.activateContractWallet user Stablecoin.contract
            Trace.callEndpoint @"initialise" hdl coin
            _ <- Trace.waitNSlots 2
            pure hdl
        mintReserveCoins rc rate hdl = do
            Trace.callEndpoint @"run step" hdl
                Input
                    { inpConversionRate = signConversionRate rate
                    , inpSCAction = MintReserveCoin rc
                    }
            void $ Trace.waitNSlots 2
        mintStableCoins sc rate hdl = do
            Trace.callEndpoint @"run step" hdl
                Input
                    { inpConversionRate = signConversionRate rate
                    , inpSCAction = MintStablecoin sc
                    }
            void $ Trace.waitNSlots 2
        redeemStableCoins sc rate hdl = do
            Trace.callEndpoint @"run step" hdl
                Input
                    { inpConversionRate = signConversionRate rate
                    , inpSCAction = MintStablecoin (negate sc)
                    }
            void $ Trace.waitNSlots 2
