{-# LANGUAGE DerivingStrategies    #-}
{-# LANGUAGE DerivingVia           #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-| The UTXO state, kept in memory by the chain index.
-}
module Plutus.ChainIndex.UtxoState(
    UtxoState(..)
    , TxUtxoBalance(..)
    , UtxoIndex
    ) where

import           Data.FingerTree         (FingerTree, Measured (..))
import           Data.Monoid             (Last (..))
import           Data.Semigroup.Generic  (GenericSemigroupMonoid (..))
import           Data.Set                (Set)
import qualified Data.Set                as Set
import           GHC.Generics            (Generic)
import           Ledger                  (Slot, TxOutRef)
import           Plutus.ChainIndex.Types (BlockId)

type UtxoIndex = FingerTree UtxoState UtxoState
instance Measured UtxoState UtxoState where
    measure = id

-- | The effect of a transaction (or a number of them) on the utxo set.
data TxUtxoBalance =
    TxUtxoBalance
        { tubUnspentOutputs       :: Set TxOutRef -- ^ Outputs newly added by the transaction(s)
        , tubUnmatchedSpentInputs :: Set TxOutRef -- ^ Outputs spent by the transaction(s)
        }
        deriving stock (Eq, Show, Generic)

instance Semigroup TxUtxoBalance where
    l <> r =
        TxUtxoBalance
            { tubUnspentOutputs       = tubUnspentOutputs r <> (tubUnspentOutputs l `Set.difference` tubUnmatchedSpentInputs r)
            , tubUnmatchedSpentInputs = (tubUnmatchedSpentInputs r `Set.difference` tubUnspentOutputs l) <> tubUnmatchedSpentInputs l
            }

instance Monoid TxUtxoBalance where
    mappend = (<>)
    mempty = TxUtxoBalance mempty mempty

-- | UTXO / ledger state, kept in memory. We are only interested in the UTXO set, everything else is stored
--   on disk. This is OK because we don't need to validate transactions when they come in.
data UtxoState =
    UtxoState
        { usTxUtxoBalance :: TxUtxoBalance
        , usSlot          :: Last (Slot, Maybe BlockId) -- ^ Last slot that we have seen + the block ID (if any)
        }
        deriving stock (Eq, Show, Generic)
        deriving (Semigroup, Monoid) via (GenericSemigroupMonoid UtxoState)
