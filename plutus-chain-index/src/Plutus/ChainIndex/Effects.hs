{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs            #-}
{-# LANGUAGE TemplateHaskell  #-}
{-| Freer effects for querying and updating the chain index state.
-}
module Plutus.ChainIndex.Effects(
    -- * Query effect
    ChainIndexQueryEffect(..)
    , datumFromHash
    , validatorFromHash
    , mintingPolicyFromHash
    , txOutFromRef
    , txFromTxId
    , utxoSetMembership
    , utxoSetAtAddress
    , getTip
    -- * Control effect
    , ChainIndexControlEffect(..)
    , appendBlock
    , rollback
    , collectGarbage
    ) where

import           Control.Monad.Freer.TH  (makeEffect)
import           Ledger                  (Datum, DatumHash, MintingPolicy, MintingPolicyHash, TxId, Validator,
                                          ValidatorHash)
import           Ledger.Credential       (Credential)
import           Ledger.Tx               (TxOut, TxOutRef)
import           Plutus.ChainIndex.Tx    (ChainIndexTx)
import           Plutus.ChainIndex.Types (Page, Tip)

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
    UtxoSetMembership :: TxOutRef -> ChainIndexQueryEffect (Tip, Bool)

    -- | Unspent outputs located at addresses with the given credential
    UtxoSetAtAddress :: Credential -> ChainIndexQueryEffect (Tip, Page TxOutRef)

    -- | Get the tip of the chain index
    GetTip :: ChainIndexQueryEffect Tip

makeEffect ''ChainIndexQueryEffect

data ChainIndexControlEffect r where

    -- | Add a new block to the chain index
    AppendBlock :: Tip -> [ChainIndexTx] -> ChainIndexControlEffect ()

    -- | Roll back to a previous state
    Rollback    :: Tip -> ChainIndexControlEffect ()

    -- | Delete all data that is not covered by current UTXOs.
    CollectGarbage :: ChainIndexControlEffect ()

makeEffect ''ChainIndexControlEffect
