{-# LANGUAGE DataKinds          #-}
{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts   #-}
{-# LANGUAGE GADTs              #-}
{-# LANGUAGE TemplateHaskell    #-}
module Wallet.Effects(
    WalletEffects
    -- * Wallet effect
    , WalletEffect(..)
    , Payment(..)
    , emptyPayment
    , submitTxn
    , ownPubKey
    , updatePaymentWithChange
    , walletSlot
    , ownOutputs
    -- * Node client
    , NodeClientEffect(..)
    , publishTx
    , getClientSlot
    -- * Signing process
    , SigningProcessEffect(..)
    , addSignatures
    -- * Chain index
    , ChainIndexEffect(..)
    , startWatching
    , watchedAddresses
    , transactionConfirmed
    ) where

import           Control.Monad.Freer.TH (makeEffect)
import           Data.Aeson             (FromJSON, ToJSON)
import qualified Data.Set               as Set
import           GHC.Generics           (Generic)
import           Ledger                 (Address, PubKey, PubKeyHash, Slot, Tx, TxId, TxIn, TxOut, Value)
import           Ledger.AddressMap      (AddressMap, UtxoMap)

-- | A payment consisting of a set of inputs to be spent, and
--   an optional change output. The size of the payment is the
--   difference between the total value of the inputs and the
--   value of the output.
data Payment =
    Payment
        { paymentInputs       :: Set.Set TxIn
        , paymentChangeOutput :: Maybe TxOut
        } deriving stock (Eq, Show, Generic)
          deriving anyclass (ToJSON, FromJSON)

-- | A payment with zero inputs and no change output
emptyPayment :: Payment
emptyPayment = Payment { paymentInputs = Set.empty, paymentChangeOutput = Nothing }

data WalletEffect r where
    SubmitTxn :: Tx -> WalletEffect ()
    OwnPubKey :: WalletEffect PubKey
    UpdatePaymentWithChange :: Value -> Payment -> WalletEffect Payment
    WalletSlot :: WalletEffect Slot
    OwnOutputs :: WalletEffect UtxoMap
makeEffect ''WalletEffect

data NodeClientEffect r where
    PublishTx :: Tx -> NodeClientEffect ()
    GetClientSlot :: NodeClientEffect Slot
makeEffect ''NodeClientEffect

data SigningProcessEffect r where
    AddSignatures :: [PubKeyHash] -> Tx -> SigningProcessEffect Tx
makeEffect ''SigningProcessEffect

-- | Access a (plutus-specific) chain index. The chain index keeps track of the
--   datums that are associated with unspent transaction outputs. Addresses that
--   are of interest need to be added with 'startWatching' before their outputs
--   show up in the 'AddressMap' returned by 'watchedAddresses'.
data ChainIndexEffect r where
    StartWatching :: Address -> ChainIndexEffect ()
    WatchedAddresses :: ChainIndexEffect AddressMap
    -- TODO: In the future we should have degrees of confirmation
    TransactionConfirmed :: TxId -> ChainIndexEffect Bool
makeEffect ''ChainIndexEffect

-- | Effects that allow contracts to interact with the blockchain
type WalletEffects =
    '[ WalletEffect
    , NodeClientEffect
    , SigningProcessEffect
    , ChainIndexEffect
    ]
