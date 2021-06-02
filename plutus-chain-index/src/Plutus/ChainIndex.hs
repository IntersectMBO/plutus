{-# LANGUAGE DerivingStrategies    #-}
{-# LANGUAGE DerivingVia           #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Plutus.ChainIndex where

import           Data.FingerTree        (FingerTree, Measured (..))
import           Data.Map               (Map)
import           Data.Semigroup.Generic (GenericSemigroupMonoid (..))
import           Data.Set               (Set)
import           GHC.Generics           (Generic)
import           Ledger                 (Datum, DatumHash, MonetaryPolicy, MonetaryPolicyHash, Slot (..), TxId, TxIn,
                                         TxOut, TxOutRef, Validator, ValidatorHash)
import           Plutus.ChainIndex.Tx   (ChainIndexTx)

data ChainIndex =
    ChainIndex
        { _ciDataMap           :: Map DatumHash Datum
        , _ciValidatorMap      :: Map ValidatorHash Validator
        , _ciMonetaryPolicyMap :: Map MonetaryPolicyHash MonetaryPolicy
        , _ciUtxoIndex         :: UtxoIndex
        }
        deriving stock (Eq, Show, Generic)

type UtxoIndex = FingerTree UtxoState UtxoState
instance Measured UtxoState UtxoState where
    measure = id

data UtxoState =
    UtxoState
        { _usTxMap            :: Map TxId ChainIndexTx
        , _usUtxoMap          :: Map TxOutRef TxOut
        , _usUnmatchedTxInSet :: Set TxIn
        , _usTip              :: BlockId
        }
        deriving stock (Eq, Show, Generic)
        deriving (Semigroup, Monoid) via (GenericSemigroupMonoid UtxoState)

newtype BlockId = BlockId (Slot, Integer)
    deriving (Eq, Show, Generic)
instance Semigroup BlockId where
    BlockId l <> BlockId r = BlockId (max l r)
instance Monoid BlockId where
    mempty = BlockId (Slot 0, 0)
