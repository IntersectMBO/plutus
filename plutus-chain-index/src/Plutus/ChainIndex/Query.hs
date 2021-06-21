{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs            #-}
{-# LANGUAGE TemplateHaskell  #-}
{-| A freer effect for querying the chain index
-}
module Plutus.ChainIndex.Query(
    ChainIndexQueryEffect(..)
    , datumFromHash
    , validatorFromHash
    , mintingPolicyFromHash
    , txOutFromRef
    , txFromTxId
    , utxoSetMembership
    , utxoSetAtAddress
    , tip
    ) where

import           Control.Monad.Freer.TH  (makeEffect)
import           Ledger                  (Datum, DatumHash, MintingPolicy, MintingPolicyHash, Slot, TxId, Validator,
                                          ValidatorHash)
import           Ledger.Credential       (Credential)
import           Ledger.Tx               (TxOut, TxOutRef)
import           Plutus.ChainIndex.Tx    (ChainIndexTx)
import           Plutus.ChainIndex.Types (BlockId, Page)

data ChainIndexQueryEffect r where

    -- | Get the datum from a datum hash (if available)
    DatumFromHash :: DatumHash -> ChainIndexQueryEffect (Maybe Datum)

    -- | Get the validator from a validator hash (if available)
    ValidatorFromHash :: ValidatorHash -> ChainIndexQueryEffect (Maybe Validator)

    -- | Get the monetary policy from an MPS hash (if available)
    MintingPolicyFromHash :: MintingPolicyHash -> ChainIndexQueryEffect (Maybe MintingPolicy)

    -- | Get the TxOut from a TxOutRef (if available)
    TxOutFromRef :: TxOutRef -> ChainIndexQueryEffect (Maybe TxOut)

    -- | Get the transaction for a tx ID
    TxFromTxId :: TxId -> ChainIndexQueryEffect (Maybe ChainIndexTx)

    -- | Whether a tx output is part of the UTXO set
    UtxoSetMembership :: TxOutRef -> ChainIndexQueryEffect (Slot, Maybe BlockId, Bool)

    -- | How many unspent outputs are located at address with the given credential
    UtxoSetAtAddress :: Credential -> ChainIndexQueryEffect (Page TxOutRef)

    -- | Get the tip of the chain index
    Tip :: ChainIndexQueryEffect (Slot, Maybe BlockId)

makeEffect ''ChainIndexQueryEffect
