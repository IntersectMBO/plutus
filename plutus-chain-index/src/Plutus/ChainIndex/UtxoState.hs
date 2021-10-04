{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE DerivingVia           #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MonoLocalBinds        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns        #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE ViewPatterns          #-}
{-| The UTXO state, kept in memory by the chain index.
-}
module Plutus.ChainIndex.UtxoState(
    UtxoState(..)
    , usTxUtxoData
    , usTip
    , TxUtxoBalance(..)
    , tubUnspentOutputs
    , tubUnmatchedSpentInputs
    , UtxoIndex
    , utxoState
    , utxoBlockCount
    , fromBlock
    , fromTx
    , isUnspentOutput
    , tip
    , viewTip
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
    , rollbackWith
    -- * Limit the UTXO index size
    , ReduceBlockCountResult(..)
    , reduceBlockCount
    ) where

import           Codec.Serialise                   (Serialise)
import           Control.Lens                      (makeLenses, view)
import           Data.Aeson                        (FromJSON, ToJSON)
import           Data.FingerTree                   (FingerTree, Measured (..))
import qualified Data.FingerTree                   as FT
import           Data.Function                     (on)
import           Data.Monoid                       (Sum (..))
import           Data.Semigroup.Generic            (GenericSemigroupMonoid (..))
import           Data.Set                          (Set)
import qualified Data.Set                          as Set
import           GHC.Generics                      (Generic)
import           Ledger                            (TxIn (txInRef), TxOutRef (..))
import           Plutus.ChainIndex.ChainIndexError (InsertUtxoFailed (..), RollbackFailed (..))
import           Plutus.ChainIndex.ChainIndexLog   (InsertUtxoPosition (..))
import           Plutus.ChainIndex.Tx              (ChainIndexTx (..), citxInputs, txOutsWithRef)
import           Plutus.ChainIndex.Types           (Point (..), Tip (..), pointsToTip)
import           Prettyprinter                     (Pretty (..))

-- | The effect of a transaction (or a number of them) on the utxo set.
data TxUtxoBalance =
    TxUtxoBalance
        { _tubUnspentOutputs       :: Set TxOutRef -- ^ Outputs newly added by the transaction(s)
        , _tubUnmatchedSpentInputs :: Set TxOutRef -- ^ Outputs spent by the transaction(s)
        }
        deriving stock (Eq, Show, Generic)
        deriving anyclass (FromJSON, ToJSON, Serialise)


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
data UtxoState a =
    UtxoState
        { _usTxUtxoData :: a -- One of 'TxUtxoBalance' or 'TxIdState'
        , _usTip        :: Tip -- ^ Tip of our chain sync client
        }
        deriving stock (Eq, Show, Generic)
        deriving (Semigroup, Monoid) via (GenericSemigroupMonoid (UtxoState a))
        deriving anyclass (FromJSON, ToJSON)

makeLenses ''UtxoState

fromTx :: ChainIndexTx -> TxUtxoBalance
fromTx tx =
    TxUtxoBalance
        { _tubUnspentOutputs = Set.fromList $ fmap snd $ txOutsWithRef tx
        , _tubUnmatchedSpentInputs = Set.mapMonotonic txInRef (view citxInputs tx)
        }

newtype BlockCount = BlockCount { getBlockCount :: Int } deriving (Semigroup, Monoid) via (Sum Int)

type UtxoIndex a = FingerTree (BlockCount, UtxoState a) (UtxoState a)
instance Monoid a => Measured (BlockCount, UtxoState a) (UtxoState a) where
    measure u = (BlockCount 1, u)

utxoState :: Monoid a => UtxoIndex a -> UtxoState a
utxoState = snd . measure

utxoBlockCount :: Monoid a => UtxoIndex a -> Int
utxoBlockCount = getBlockCount . fst . measure

-- | Whether a 'TxOutRef' is a member of the UTXO set (ie. unspent)
isUnspentOutput :: TxOutRef -> UtxoState TxUtxoBalance -> Bool
isUnspentOutput r = Set.member r . view (usTxUtxoData . tubUnspentOutputs)

tip :: UtxoState a -> Tip
tip = view usTip

viewTip :: Monoid a => UtxoIndex a -> Tip
viewTip = tip . utxoState

instance Eq a => Ord (UtxoState a) where
    compare = compare `on` tip

-- | The UTXO set
unspentOutputs :: UtxoState TxUtxoBalance -> Set TxOutRef
unspentOutputs = view (usTxUtxoData . tubUnspentOutputs)

-- | 'UtxoIndex' for a single block
fromBlock :: Tip -> [ChainIndexTx] -> UtxoState TxUtxoBalance
fromBlock tip_ transactions =
    UtxoState
            { _usTxUtxoData = foldMap fromTx transactions
            , _usTip        = tip_
            }

data InsertUtxoSuccess a =
    InsertUtxoSuccess
        { newIndex       :: UtxoIndex a
        , insertPosition :: InsertUtxoPosition
        }

instance Pretty (InsertUtxoSuccess a) where
  pretty = \case
    InsertUtxoSuccess _ insertPosition -> pretty insertPosition

-- | Insert a 'UtxoState' into the index
insert ::
       ( Monoid a
       , Eq a
       )
       => UtxoState a
       -> UtxoIndex a
       -> Either InsertUtxoFailed (InsertUtxoSuccess a)
insert   UtxoState{_usTip=TipAtGenesis} _ = Left InsertUtxoNoTip
insert s@UtxoState{_usTip=thisTip} ix =
    let (before, after) = FT.split ((s <=) . snd) ix
    in case tip (utxoState after) of
        TipAtGenesis -> Right $ InsertUtxoSuccess{newIndex = before FT.|> s, insertPosition = InsertAtEnd}
        t | t > thisTip -> Right $ InsertUtxoSuccess{newIndex = (before FT.|> s) <> after, insertPosition = InsertBeforeEnd}
          | otherwise   -> Left  $ DuplicateBlock t

data RollbackResult a =
    RollbackResult
        { newTip          :: Tip
        , rolledBackIndex :: UtxoIndex a
        }

-- | Perform a rollback on the utxo index
rollback :: Point
         -> UtxoIndex TxUtxoBalance
         -> Either RollbackFailed (RollbackResult TxUtxoBalance)
rollback = rollbackWith const

-- | Perform a rollback on the utxo index, with a callback to calculate the new index.
rollbackWith
    :: Monoid a
    => (UtxoIndex a -> UtxoIndex a -> UtxoIndex a) -- ^ Calculate the new index given the index before and the index after the rollback point.
    -> Point
    -> UtxoIndex a
    -> Either RollbackFailed (RollbackResult a)
rollbackWith _ PointAtGenesis (viewTip -> TipAtGenesis) = Right (RollbackResult TipAtGenesis mempty)
rollbackWith _ _ (viewTip -> TipAtGenesis) = Left RollbackNoTip
rollbackWith f targetPoint idx@(viewTip -> currentTip)
    -- Already at the target point
    |  targetPoint `pointsToTip` currentTip =
        Right RollbackResult{newTip=currentTip, rolledBackIndex=idx}
    -- The rollback happened sometime after the current tip.
    | not (targetPoint `pointLessThanTip` currentTip) =
        Left TipMismatch{foundTip=currentTip, targetPoint}
    | otherwise = do
        let (before, after) = FT.split ((targetPoint `pointLessThanTip`) . tip . snd) idx

        case viewTip before of
            TipAtGenesis -> Left $ OldPointNotFound targetPoint
            oldTip | targetPoint `pointsToTip` oldTip ->
                       Right RollbackResult{newTip=oldTip, rolledBackIndex=f before after}
                   | otherwise                        ->
                       Left  TipMismatch{foundTip=oldTip, targetPoint=targetPoint}
    where
      pointLessThanTip :: Point -> Tip -> Bool
      pointLessThanTip PointAtGenesis  _               = True
      pointLessThanTip (Point pSlot _) (Tip tSlot _ _) = pSlot < tSlot
      pointLessThanTip _               TipAtGenesis    = False

data ReduceBlockCountResult a
    = BlockCountNotReduced
    | ReduceBlockCountResult
        { reducedIndex  :: UtxoIndex a
        , combinedState :: UtxoState a
        }

-- | Reduce the number of 'UtxoState's. The given number is the minimum, the index is reduced when it larger than twice that size.
-- The new index is prefixed with one 'UtxoState' that contains the combined state of the removed 'UtxoState's.
reduceBlockCount :: Monoid a => Int -> UtxoIndex a -> ReduceBlockCountResult a
reduceBlockCount minCount ix
    | utxoBlockCount ix <= 2 * minCount = BlockCountNotReduced
    | otherwise =
        let (old, keep) = FT.split ((> (utxoBlockCount ix - minCount)) . getBlockCount . fst) ix
            combinedState = utxoState old
        in ReduceBlockCountResult
            { reducedIndex = combinedState FT.<| keep
            , combinedState = combinedState
            }
