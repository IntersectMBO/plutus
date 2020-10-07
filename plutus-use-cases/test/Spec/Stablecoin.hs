{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE GADTs             #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications  #-}

module Spec.Stablecoin(
    tests
    ) where


import           Language.Plutus.Contract.Test
import           Language.PlutusTx.Lattice
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
        Stablecoin.contract
        (fundsAtAddress stablecoinAddress (== (initialDeposit <> initialFee))
        /\ assertNoFailedTransactions
        /\ walletFundsChange user (Stablecoin.reserveCoins coin 100 <> negate (initialDeposit <> initialFee))
        )
        (initialise
        >> mintReserveCoins (RC 100) one
        )

    , checkPredicate "mint reservecoins and stablecoins"
        Stablecoin.contract
        (fundsAtAddress stablecoinAddress (== (initialDeposit <> initialFee <> Ada.lovelaceValueOf 50))
        /\ assertNoFailedTransactions
        /\ walletFundsChange user (Stablecoin.stableCoins coin 50 <> Stablecoin.reserveCoins coin 100 <> negate (initialDeposit <> initialFee <> Ada.lovelaceValueOf 50))
        )
        (initialise
        >> mintReserveCoins (RC 100) one
        -- Mint 50 stablecoins at a rate of 1 Ada: 1 USD
        >> mintStableCoins (SC 50) one
        )

    , checkPredicate "mint reservecoins, stablecoins and redeem stablecoin at a different price"
        Stablecoin.contract
        (fundsAtAddress stablecoinAddress (== (initialDeposit <> initialFee <> Ada.lovelaceValueOf 30))
        /\ assertNoFailedTransactions
        /\ walletFundsChange user (Stablecoin.stableCoins coin 40 <> Stablecoin.reserveCoins coin 100 <> negate (initialDeposit <> initialFee <> Ada.lovelaceValueOf 30))
        )
        (initialise
        >> mintReserveCoins (RC 100) one
        >> mintStableCoins (SC 50) one
        -- redeem 10 stablecoins at an exchange rate of 2 Ada : 1 USD (so we get 20 lovelace from the bank)
        >> redeemStableCoins (SC 10) (Ratio.fromInteger 2)
        )
    ] where
        initialise = do
            callEndpoint @"initialise" user coin
            handleBlockchainEvents user
            addBlocks 1
            handleBlockchainEvents user
            addBlocks 1
        mintReserveCoins rc rate = do
            callEndpoint @"run step" user
                Input
                    { inpConversionRate = signConversionRate rate
                    , inpSCAction = MintReserveCoin rc
                    }
            handleBlockchainEvents user
            addBlocks 1
            handleBlockchainEvents user
        mintStableCoins sc rate = do
            callEndpoint @"run step" user
                Input
                    { inpConversionRate = signConversionRate rate
                    , inpSCAction = MintStablecoin sc
                    }
            handleBlockchainEvents user
            addBlocks 1
            handleBlockchainEvents user
        redeemStableCoins sc rate = do
            callEndpoint @"run step" user
                Input
                    { inpConversionRate = signConversionRate rate
                    , inpSCAction = MintStablecoin (negate sc)
                    }
            handleBlockchainEvents user
            addBlocks 1
            handleBlockchainEvents user
