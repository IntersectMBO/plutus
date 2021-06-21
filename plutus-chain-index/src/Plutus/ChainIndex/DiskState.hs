{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE DerivingStrategies #-}
{-| The part of the chain index that is kept on disk.
-}
module Plutus.ChainIndex.DiskState(
    ChainIndexDiskState
) where

import           Data.Map             (Map)
import           Data.Set             (Set)
import           GHC.Generics         (Generic)
import           Ledger               (TxOutRef)
import           Ledger.Credential    (Credential)
import           Ledger.Scripts       (Datum, DatumHash, MintingPolicy, MintingPolicyHash, Validator, ValidatorHash)
import           Ledger.TxId          (TxId)
import           Plutus.ChainIndex.Tx (ChainIndexTx)

-- | Data that we keep on disk. (This type is used for testing only - we need
--   other structures for the disk-backed storage)
data ChainIndexDiskState =
    ChainIndexDiskState
        { _ciDataMap          :: Map DatumHash Datum
        , _ciValidatorMap     :: Map ValidatorHash Validator
        , _ciMintingPolicyMap :: Map MintingPolicyHash MintingPolicy
        , _ciTxMap            :: Map TxId ChainIndexTx
        , _ciAddressMap       :: Map Credential (Set TxOutRef)
        }
        deriving stock (Eq, Show, Generic)
