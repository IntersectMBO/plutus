{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE DeriveAnyClass    #-}
{-# LANGUAGE DeriveGeneric     #-}
{-# LANGUAGE DerivingVia       #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE GADTs             #-}
{-# LANGUAGE KindSignatures    #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE NamedFieldPuns    #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell   #-}
module Wallet.Effects(
    -- * Wallet effect
    WalletEffect(..)
    , submitTxn
    , ownPubKey
    , balanceTx
    , totalFunds
    , walletAddSignature
    -- * Node client
    , NodeClientEffect(..)
    , publishTx
    , getClientSlot
    , getClientSlotConfig
    ) where

import           Control.Monad.Freer.TH      (makeEffect)
import           Ledger                      (PubKey, Slot, Tx, Value)
import           Ledger.Constraints.OffChain (UnbalancedTx)
import           Ledger.TimeSlot             (SlotConfig)
import           Wallet.Emulator.Error       (WalletAPIError)

data WalletEffect r where
    SubmitTxn :: Tx -> WalletEffect ()
    OwnPubKey :: WalletEffect PubKey
    BalanceTx :: UnbalancedTx -> WalletEffect (Either WalletAPIError Tx)
    TotalFunds :: WalletEffect Value -- ^ Total of all funds that are in the wallet (incl. tokens)
    WalletAddSignature :: Tx -> WalletEffect Tx
makeEffect ''WalletEffect

data NodeClientEffect r where
    PublishTx :: Tx -> NodeClientEffect ()
    GetClientSlot :: NodeClientEffect Slot
    GetClientSlotConfig :: NodeClientEffect SlotConfig
makeEffect ''NodeClientEffect
