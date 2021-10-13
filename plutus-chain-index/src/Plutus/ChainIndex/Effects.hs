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
    , stakeValidatorFromHash
    , redeemerFromHash
    , txOutFromRef
    , txFromTxId
    , utxoSetMembership
    , utxoSetAtAddress
    , utxoSetWithCurrency
    , getTip
    -- * Control effect
    , ChainIndexControlEffect(..)
    , appendBlock
    , rollback
    , resumeSync
    , collectGarbage
    , getDiagnostics
    ) where

import           Control.Monad.Freer.Extras.Pagination (Page, PageQuery)
import           Control.Monad.Freer.TH                (makeEffect)
import           Ledger                                (AssetClass, Datum, DatumHash, MintingPolicy, MintingPolicyHash,
                                                        Redeemer, RedeemerHash, StakeValidator, StakeValidatorHash,
                                                        TxId, Validator, ValidatorHash)
import           Ledger.Credential                     (Credential)
import           Ledger.Tx                             (ChainIndexTxOut, TxOutRef)
import           Plutus.ChainIndex.Tx                  (ChainIndexTx)
import           Plutus.ChainIndex.Types               (Diagnostics, Point, Tip)

data ChainIndexQueryEffect r where

    -- | Get the datum from a datum hash (if available)
    DatumFromHash :: DatumHash -> ChainIndexQueryEffect (Maybe Datum)

    -- | Get the validator from a validator hash (if available)
    ValidatorFromHash :: ValidatorHash -> ChainIndexQueryEffect (Maybe Validator)

    -- | Get the monetary policy from an MPS hash (if available)
    MintingPolicyFromHash :: MintingPolicyHash -> ChainIndexQueryEffect (Maybe MintingPolicy)

    -- | Get the redeemer from a redeemer hash (if available)
    RedeemerFromHash :: RedeemerHash -> ChainIndexQueryEffect (Maybe Redeemer)

    -- | Get the stake validator from a stake validator hash (if available)
    StakeValidatorFromHash :: StakeValidatorHash -> ChainIndexQueryEffect (Maybe StakeValidator)

    -- | Get the TxOut from a TxOutRef (if available)
    TxOutFromRef :: TxOutRef -> ChainIndexQueryEffect (Maybe ChainIndexTxOut)

    -- | Get the transaction for a tx ID
    TxFromTxId :: TxId -> ChainIndexQueryEffect (Maybe ChainIndexTx)

    -- | Whether a tx output is part of the UTXO set
    UtxoSetMembership :: TxOutRef -> ChainIndexQueryEffect (Tip, Bool)

    -- | Unspent outputs located at addresses with the given credential.
    UtxoSetAtAddress :: PageQuery TxOutRef -> Credential -> ChainIndexQueryEffect (Tip, Page TxOutRef)

    -- | Unspent outputs containing a specific currency ('AssetClass').
    --
    -- Note that requesting unspent outputs containing Ada should not return
    -- anything, as this request will always return all unspent outputs.
    UtxoSetWithCurrency :: PageQuery TxOutRef -> AssetClass -> ChainIndexQueryEffect (Tip, Page TxOutRef)

    -- | Get the tip of the chain index
    GetTip :: ChainIndexQueryEffect Tip

makeEffect ''ChainIndexQueryEffect

data ChainIndexControlEffect r where

    -- | Add a new block to the chain index by giving a new tip and list of tx.
    AppendBlock :: Tip -> [ChainIndexTx] -> ChainIndexControlEffect ()

    -- | Roll back to a previous state (previous tip)
    Rollback    :: Point -> ChainIndexControlEffect ()

    -- | Resume syncing from a certain point
    ResumeSync  :: Point -> ChainIndexControlEffect ()

    -- | Delete all data that is not covered by current UTxOs.
    CollectGarbage :: ChainIndexControlEffect ()

    GetDiagnostics :: ChainIndexControlEffect Diagnostics

makeEffect ''ChainIndexControlEffect
