{-# LANGUAGE RecordWildCards #-}
{-| The chain index' version of a transaction
-}
module Plutus.ChainIndex.Tx(
    ChainIndexTx(..)
    , fromOnChainTx
    ) where

import           Data.Map (Map)
import           Data.Set (Set)
import           Ledger   (Datum, DatumHash, OnChainTx (..), SlotRange, Tx (..), TxId, TxIn, TxOut, txId)

data ChainIndexTx = ChainIndexTx {
    citxId         :: TxId,
    citxInputs     :: Set TxIn,
    citxOutputs    :: [TxOut],
    citxValidRange :: !SlotRange,
    citxData       :: Map DatumHash Datum
    } deriving (Show, Eq)

fromOnChainTx :: OnChainTx -> ChainIndexTx
fromOnChainTx (Valid tx@Tx{..})   = ChainIndexTx (txId tx) txInputs txOutputs txValidRange txData
fromOnChainTx (Invalid tx@Tx{..}) = ChainIndexTx (txId tx) txCollateral mempty txValidRange mempty
