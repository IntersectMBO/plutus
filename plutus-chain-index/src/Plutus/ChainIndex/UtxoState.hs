{-# LANGUAGE DerivingStrategies    #-}
{-# LANGUAGE DerivingVia           #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns        #-}
{-# LANGUAGE TemplateHaskell       #-}
{-| The UTXO state, kept in memory by the chain index.
-}
module Plutus.ChainIndex.UtxoState(
    UtxoState(..)
    , usTxUtxoBalance
    , usTip
    , TxUtxoBalance(..)
    , tubUnspentOutputs
    , tubUnmatchedSpentInputs
    , UtxoIndex
    , utxoState
    , fromBlock
    , fromTx
    , isUnspentOutput
    , tip
    , unspentOutputs
    -- * Extending the UTXO index
    , InsertUtxoPosition(..)
    , InsertUtxoSuccess(..)
    , InsertUtxoFailed(..)
    , insert
    -- * Rollbacks
    , RollbackFailed(..)
    , RollbackResult(..)
    , rollback
    ) where

import           Control.Lens            (makeLenses, view)
import           Data.FingerTree         (FingerTree, Measured (..))
import qualified Data.FingerTree         as FT
import           Data.Monoid             (Last (..))
import           Data.Semigroup.Generic  (GenericSemigroupMonoid (..))
import           Data.Set                (Set)
import qualified Data.Set                as Set
import           GHC.Generics            (Generic)
import           Ledger                  (TxIn (txInRef), TxOutRef (..))
import           Plutus.ChainIndex.Tx    (ChainIndexTx (..), txOutRefs)
import           Plutus.ChainIndex.Types (Tip (..))

-- | The effect of a transaction (or a number of them) on the utxo set.
data TxUtxoBalance =
    TxUtxoBalance
        { _tubUnspentOutputs       :: Set TxOutRef -- ^ Outputs newly added by the transaction(s)
        , _tubUnmatchedSpentInputs :: Set TxOutRef -- ^ Outputs spent by the transaction(s)
        }
        deriving stock (Eq, Show, Generic)

makeLenses ''TxUtxoBalance

instance Semigroup TxUtxoBalance where
    l <> r =
        TxUtxoBalance
            { _tubUnspentOutputs       = _tubUnspentOutputs r <> (_tubUnspentOutputs l `Set.difference` _tubUnmatchedSpentInputs r)
            , _tubUnmatchedSpentInputs = (_tubUnmatchedSpentInputs r `Set.difference` _tubUnspentOutputs l) <> _tubUnmatchedSpentInputs l
            }

instance Monoid TxUtxoBalance where
    mappend = (<>)
    mempty = TxUtxoBalance mempty mempty

-- | UTXO / ledger state, kept in memory. We are only interested in the UTXO set, everything else is stored
--   on disk. This is OK because we don't need to validate transactions when they come in.
data UtxoState =
    UtxoState
        { _usTxUtxoBalance :: TxUtxoBalance
        , _usTip           :: Last Tip -- ^ Tip of our chain sync client
        }
        deriving stock (Eq, Show, Generic)
        deriving (Semigroup, Monoid) via (GenericSemigroupMonoid UtxoState)

makeLenses ''UtxoState

fromTx :: ChainIndexTx -> TxUtxoBalance
fromTx tx@ChainIndexTx{_citxInputs} =
    TxUtxoBalance
        { _tubUnspentOutputs = Set.fromList $ fmap snd $ txOutRefs tx
        , _tubUnmatchedSpentInputs = Set.mapMonotonic txInRef _citxInputs
        }

type UtxoIndex = FingerTree UtxoState UtxoState
instance Measured UtxoState UtxoState where
    measure = id

utxoState :: UtxoIndex -> UtxoState
utxoState = measure

-- | Whether a 'TxOutRef' is a member of the UTXO set (ie. unspent)
isUnspentOutput :: TxOutRef -> UtxoState -> Bool
isUnspentOutput r = Set.member r . view (usTxUtxoBalance . tubUnspentOutputs)

tip :: UtxoState -> Maybe Tip
tip = getLast . view usTip

-- | The UTXO set
unspentOutputs :: UtxoState -> Set TxOutRef
unspentOutputs = view (usTxUtxoBalance . tubUnspentOutputs)

-- | 'UtxoIndex' for a single block
fromBlock :: Tip -> [ChainIndexTx] -> UtxoState
fromBlock tip_ transactions =
    UtxoState
            { _usTxUtxoBalance = foldMap fromTx transactions
            , _usTip           = Last (Just tip_)
            }

-- | Outcome of inserting a 'UtxoState' into the utxo index
data InsertUtxoPosition =
    InsertAtEnd -- ^ The utxo state was added to the end. Returns the new index
    | InsertBeforeEnd -- ^ The utxo state was added somewhere before the end. Returns the new index and the tip
    deriving stock (Eq, Ord, Show)

data InsertUtxoSuccess =
    InsertUtxoSuccess
        { newIndex       :: UtxoIndex
        , insertPosition :: InsertUtxoPosition
        }

-- | UTXO state could not be inserted into the chain index
data InsertUtxoFailed =
    DuplicateBlock Tip -- ^ Insertion failed as there was already a block with the given number
    | InsertUtxoNoTip -- ^ The '_usTip' field of the argument was 'Last Nothing'
    deriving stock (Eq, Ord, Show)

-- | Insert a 'UtxoState' into the index
insert :: UtxoState -> UtxoIndex -> Either InsertUtxoFailed InsertUtxoSuccess
insert UtxoState{_usTip=Last Nothing} _ = Left InsertUtxoNoTip
insert s@UtxoState{_usTip=Last(Just Tip{tipBlockNo=thisBlockNo})} ix =
    let gt UtxoState{_usTip=Last otherTip} = maybe False (\Tip{tipBlockNo=otherBlockNo} -> otherBlockNo >= thisBlockNo) otherTip
        (before, after) = FT.split gt ix
    in case _usTip (measure after) of
        Last Nothing -> Right $ InsertUtxoSuccess{newIndex = before FT.|> s, insertPosition = InsertAtEnd}
        Last (Just t@Tip{tipBlockNo=otherBlockNo})
            | otherBlockNo > thisBlockNo -> Right $ InsertUtxoSuccess{newIndex = (before FT.|> s) <> after, insertPosition = InsertBeforeEnd}
            | otherwise -> Left $ DuplicateBlock t

-- | Reason why the 'rollback' operation failed
data RollbackFailed =
    RollbackNoTip  -- ^ Rollback failed because the utxo index had no tip (not synchronised)
    | TipMismatch { foundTip :: Tip, targetTip :: Tip } -- ^ Unable to roll back to 'expectedTip' because the tip at that position was different
    | OldTipNotFound Tip -- ^ Unable to find the old tip
    deriving stock (Eq, Ord, Show)

data RollbackResult =
    RollbackResult
        { newTip          :: Tip
        , rolledBackIndex :: UtxoIndex
        }

-- | Perform a rollback on the utxo index
rollback :: Tip -> UtxoIndex -> Either RollbackFailed RollbackResult
rollback targetTip@Tip{tipBlockNo=targetBlockNo} idx = case tip (measure idx) of
    Nothing -> Left RollbackNoTip
    Just currentTip@Tip{tipBlockNo=currentBlockNo}
        | currentBlockNo < targetBlockNo -> Left TipMismatch{foundTip=currentTip, targetTip}
        | otherwise -> do
            let gt UtxoState{_usTip=Last otherTip} = maybe False (\Tip{tipBlockNo=otherBlockNo} -> otherBlockNo > targetBlockNo) otherTip
                (before, _) = FT.split gt idx

            case tip (measure before) of
                Nothing -> Left $ OldTipNotFound targetTip
                Just oldTip | oldTip == targetTip -> Right RollbackResult{newTip=oldTip, rolledBackIndex=before}
                            | otherwise           -> Left $ TipMismatch{foundTip=oldTip, targetTip}
