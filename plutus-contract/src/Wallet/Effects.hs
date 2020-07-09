{-# LANGUAGE DataKinds          #-}
{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts   #-}
{-# LANGUAGE GADTs              #-}
{-# LANGUAGE NamedFieldPuns     #-}
{-# LANGUAGE OverloadedStrings  #-}
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
    , AddressChangeRequest(..)
    , AddressChangeResponse(..)
    , startWatching
    , watchedAddresses
    , confirmedBlocks
    , transactionConfirmed
    , nextTx
    ) where

import           Control.Monad.Freer.TH    (makeEffect)
import           Data.Aeson                (FromJSON, ToJSON)
import qualified Data.Set                  as Set
import           Data.Text.Prettyprint.Doc
import           GHC.Generics              (Generic)
import           Ledger                    (Address, PubKey, PubKeyHash, Slot, Tx, TxId, TxIn, TxOut, Value, txId)
import           Ledger.AddressMap         (AddressMap, UtxoMap)

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

-- | Information about transactions that spend or produce an output at
--   an address in a slot.
data AddressChangeResponse =
    AddressChangeResponse
        { acrAddress :: Address -- ^ The address
        , acrSlot    :: Slot -- ^ The slot
        , acrTxns    :: [Tx] -- ^ Transactions that were validated in the slot and spent or produced at least one output at the address.
        }
        deriving stock (Eq, Generic, Show)
        deriving anyclass (ToJSON, FromJSON)

instance Pretty AddressChangeResponse where
    pretty AddressChangeResponse{acrAddress, acrTxns, acrSlot} =
        hang 2 $ vsep
            [ "Address:" <+> pretty acrAddress
            , "Slot:" <+> pretty acrSlot
            , "Tx IDs:" <+> pretty (txId <$> acrTxns)
            ]

-- | Request for information about transactions that spend or produce
--   outputs at a specific address in a slot.
data AddressChangeRequest =
    AddressChangeRequest
        { acreqSlot    :: Slot -- ^ The slot
        , acreqAddress :: Address -- ^ The address
        }
        deriving stock (Eq, Generic, Show, Ord)
        deriving anyclass (ToJSON, FromJSON)

instance Pretty AddressChangeRequest where
    pretty AddressChangeRequest{acreqSlot, acreqAddress} =
        hang 2 $ vsep
            [ "Slot:" <+> pretty acreqSlot
            , "Address:" <+> pretty acreqAddress
            ]

{-| Access the chain index. The chain index keeps track of the
    datums that are associated with unspent transaction outputs. Addresses that
    are of interest need to be added with 'startWatching' before their outputs
    show up in the 'AddressMap' returned by 'watchedAddresses'.
-}
data ChainIndexEffect r where
    StartWatching :: Address -> ChainIndexEffect ()
    WatchedAddresses :: ChainIndexEffect AddressMap
    ConfirmedBlocks :: ChainIndexEffect [[Tx]]
    -- TODO: In the future we should have degrees of confirmation
    TransactionConfirmed :: TxId -> ChainIndexEffect Bool
    NextTx :: AddressChangeRequest -> ChainIndexEffect AddressChangeResponse
makeEffect ''ChainIndexEffect

-- | Effects that allow contracts to interact with the blockchain
type WalletEffects =
    '[ WalletEffect
    , NodeClientEffect
    , SigningProcessEffect
    , ChainIndexEffect
    ]
