{-# LANGUAGE DerivingStrategies    #-}
{-# LANGUAGE DerivingVia           #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-| The UTXO state, kept in memory by the chain index.
-}
module Plutus.ChainIndex.UtxoState(
    UtxoState
    , UtxoIndex
    ) where

import           Data.FingerTree         (FingerTree, Measured (..))
import           Data.Monoid             (Last (..))
import           Data.Set                (Set)
import qualified Data.Set                as Set
import           GHC.Generics            (Generic)
import           Ledger                  (Slot, TxOutRef)
import           Plutus.ChainIndex.Types (BlockId)

type UtxoIndex = FingerTree UtxoState UtxoState
instance Measured UtxoState UtxoState where
    measure = id

-- | UTXO / ledger state, kept in memory. We are only interested in the UTXO set, everything else is stored
--   on disk. This is OK because we don't need to validate transactions when they come in.
data UtxoState =
    UtxoState
        { _usUnspentOutputs        :: Set TxOutRef -- ^ Outputs that have not been spent yet
        , _usUnmatchedSpentOutputs :: Set TxOutRef -- ^ Outputs that we have seen a spending transaction for, but not a producing transaction
        , _usSlot                  :: Last Slot -- ^ Last slot that we have seen
        , _usBlockId               :: Last BlockId -- ^ Last block ID
        }
        deriving stock (Eq, Show, Generic)

instance Semigroup UtxoState where
    l <> r =
        -- (<>) works like an inverse semigroup on the _usUnspentOutputs and _usUnmatchedSpentOutputs fields
        -- it is not commutative.
        -- TODO: Add tests
        let newlySpent = _usUnmatchedSpentOutputs r `Set.difference` _usUnmatchedSpentOutputs l in
        UtxoState
            { _usUnspentOutputs = (_usUnspentOutputs l <> _usUnspentOutputs r) `Set.difference` newlySpent
            , _usUnmatchedSpentOutputs = _usUnmatchedSpentOutputs l <> (_usUnmatchedSpentOutputs r `Set.difference` newlySpent)
            , _usSlot = _usSlot r
            , _usBlockId = _usBlockId r
            }

instance Monoid UtxoState where
    mappend = (<>)
    mempty = UtxoState mempty mempty mempty mempty
