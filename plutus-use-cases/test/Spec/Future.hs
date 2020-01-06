{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE MonoLocalBinds      #-}
{-# LANGUAGE NamedFieldPuns      #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeApplications    #-}
{-# OPTIONS_GHC -fno-warn-incomplete-uni-patterns #-}
module Spec.Future(tests, theFuture, accounts) where

import           Test.Tasty
import qualified Test.Tasty.HUnit                                      as HUnit

import qualified Spec.Lib                                              as Lib
import           Spec.TokenAccount                                     (assertAccountBalance)

import           Ledger                                                (OracleValue (..))
import qualified Ledger
import qualified Ledger.Ada                                            as Ada
import           Ledger.Crypto                                         (PubKey (..))
import           Ledger.Value                                          (CurrencySymbol, Value, scale)

import           Language.Plutus.Contract.Test
import qualified Language.PlutusTx                                     as PlutusTx
import           Language.PlutusTx.Coordination.Contracts.Future       (Future (..), FutureAccounts (..), FutureError,
                                                                        FutureSchema, FutureSetup (..), Role (..))
import qualified Language.PlutusTx.Coordination.Contracts.Future       as F
import           Language.PlutusTx.Coordination.Contracts.TokenAccount (Account (..))
import           Language.PlutusTx.Lattice

tests :: TestTree
tests =
    testGroup "futures"
    [ checkPredicate @FutureSchema "can initialise and obtain tokens"
        (F.futureContract theFuture)
        (walletFundsChange w1 (scale (-1) (F.initialMargin theFuture) <> F.tokenFor Short accounts)
        /\ walletFundsChange w2 (scale (-1) (F.initialMargin theFuture) <> F.tokenFor Long accounts))
        ( initContract >> joinFuture )

    , checkPredicate @FutureSchema "can increase margin"
        (F.futureContract theFuture)
        (assertAccountBalance (ftoShort accounts) (== (Ada.lovelaceValueOf 1936))
        /\ assertAccountBalance (ftoLong accounts) (== (Ada.lovelaceValueOf 2410)))
        ( initContract
        >> joinFuture
        >> addBlocks 20
        >> increaseMargin
        >> addBlocks 75
        >> payOut)

    , checkPredicate @FutureSchema "can settle early"
        (F.futureContract theFuture)
        (assertAccountBalance (ftoShort accounts) (== (Ada.lovelaceValueOf 0))
        /\ assertAccountBalance (ftoLong accounts) (== (Ada.lovelaceValueOf 4246)))
        ( initContract
        >> joinFuture
        >> addBlocks 20
        >> settleEarly)

    , checkPredicate @FutureSchema "can pay out"
        (F.futureContract theFuture)
        (assertAccountBalance (ftoShort accounts) (== (Ada.lovelaceValueOf 1936))
        /\ assertAccountBalance (ftoLong accounts) (== (Ada.lovelaceValueOf 2310)))
        ( initContract
        >> joinFuture
        >> addBlocks 93
        >> payOut)

    , Lib.goldenPir "test/Spec/future.pir" $$(PlutusTx.compile [|| F.futureStateMachine ||])

    , HUnit.testCase "script size is reasonable" (Lib.reasonable (F.validator theFuture accounts) 50000)

    ]

setup :: FutureSetup
setup =
    FutureSetup
        { shortPK = walletPubKey (Wallet 1)
        , longPK = walletPubKey (Wallet 2)
        , contractStart = 15
        }

w1 :: Wallet
w1 = Wallet 1

w2 :: Wallet
w2 = Wallet 2

-- | A futures contract over 187 units with a forward price of 1233 Lovelace,
--   due at slot #100.
theFuture :: Future
theFuture = Future {
    ftDeliveryDate  = Ledger.Slot 100,
    ftUnits         = units,
    ftUnitPrice     = forwardPrice,
    ftInitialMargin = Ada.lovelaceValueOf 800,
    ftPriceOracle   = oracle,
    ftMarginPenalty = penalty
    }

-- | This is the address of contract 'theFuture', initialised by wallet 1
tokenCurrency :: CurrencySymbol
tokenCurrency = "ae91bd641d7cff3dbaed8092663175574b01d76ea0ce1fca8086f5af50833123"

-- | After this trace, the initial margin of wallet 1, and the two tokens,
--   are locked by the contract.
initContract :: MonadEmulator (TraceError FutureError) m => ContractTrace FutureSchema FutureError m a ()
initContract = do
    callEndpoint @"initialise-future" (Wallet 1) (setup, Short)
    handleBlockchainEvents (Wallet 1)

-- | Calls the "join-future" endpoint for wallet 2 and processes
--   all resulting transactions.
joinFuture :: MonadEmulator (TraceError FutureError) m => ContractTrace FutureSchema FutureError m a ()
joinFuture = do
    callEndpoint @"join-future" (Wallet 2) (accounts, setup)
    handleBlockchainEvents (Wallet 2)
    notifySlot w1
    handleUtxoQueries (Wallet 1)
    handleBlockchainEvents (Wallet 1)
    handleBlockchainEvents (Wallet 2)

-- | Calls the "settle-future" endpoint for wallet 2 and processes
--   all resulting transactions.
payOut :: MonadEmulator (TraceError FutureError) m => ContractTrace FutureSchema FutureError m a ()
payOut = do
    let
        spotPrice = Ada.lovelaceValueOf 1124
        ov = OracleValue oracle (ftDeliveryDate theFuture) spotPrice
    callEndpoint @"settle-future" (Wallet 2) ov
    handleUtxoQueries (Wallet 2)
    handleBlockchainEvents (Wallet 2)
    addBlocks 1
    handleBlockchainEvents (Wallet 2)

-- | Margin penalty
penalty :: Value
penalty = Ada.lovelaceValueOf 1000

-- | The forward price agreed at the beginning of the contract.
forwardPrice :: Value
forwardPrice = Ada.lovelaceValueOf 1123

-- | How many units of the underlying asset are covered by the contract.
units :: Integer
units = 187

oracle :: PubKey
oracle = walletPubKey (Wallet 10)

accounts :: FutureAccounts
accounts = F.mkAccounts
            (Account (tokenCurrency, "long"))
            (Account (tokenCurrency, "short"))

increaseMargin :: MonadEmulator (TraceError FutureError) m => ContractTrace FutureSchema FutureError m a ()
increaseMargin = do
    callEndpoint @"increase-margin" (Wallet 2) (Ada.lovelaceValueOf 100, Long)
    handleBlockchainEvents (Wallet 2)

settleEarly :: MonadEmulator (TraceError FutureError) m => ContractTrace FutureSchema FutureError m a ()
settleEarly = do
    let
        spotPrice = Ada.lovelaceValueOf 11240
        ov = OracleValue oracle (Ledger.Slot 25) spotPrice
    callEndpoint @"settle-early" (Wallet 2) ov
    handleBlockchainEvents (Wallet 2)
