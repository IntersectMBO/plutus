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
    WalletEffects
    -- * Wallet effect
    , WalletEffect(..)
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
    -- * Chain index
    , ChainIndexEffect(..)
    , AddressChangeRequest(..)
    , AddressChangeResponse(..)
    , startWatching
    , watchedAddresses
    , confirmedBlocks
    , addressChanged
    ) where

import           Control.Monad.Freer.TH      (makeEffect)
import           Ledger                      (Address, Block, PubKey, Slot, Tx, Value)
import           Ledger.AddressMap           (AddressMap)
import           Ledger.Constraints.OffChain (UnbalancedTx)
import           Ledger.TimeSlot             (SlotConfig)
import           Wallet.Emulator.Error       (WalletAPIError)
import           Wallet.Types                (AddressChangeRequest (..), AddressChangeResponse (..))

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

{-| Access the chain index. The chain index keeps track of the
    datums that are associated with unspent transaction outputs. Addresses that
    are of interest need to be added with 'startWatching' before their outputs
    show up in the 'AddressMap' returned by 'watchedAddresses'.
-}
data ChainIndexEffect r where
    StartWatching :: Address -> ChainIndexEffect ()
    WatchedAddresses :: ChainIndexEffect AddressMap
    ConfirmedBlocks :: ChainIndexEffect [Block]
    AddressChanged :: AddressChangeRequest -> ChainIndexEffect AddressChangeResponse
makeEffect ''ChainIndexEffect

-- | Effects that allow contracts to interact with the blockchain
type WalletEffects =
    '[ WalletEffect
    , NodeClientEffect
    , ChainIndexEffect
    ]
