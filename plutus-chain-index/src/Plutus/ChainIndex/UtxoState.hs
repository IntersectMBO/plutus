{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE DerivingStrategies    #-}
{-# LANGUAGE DerivingVia           #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns        #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE ViewPatterns          #-}
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
import           Data.Aeson              (FromJSON, ToJSON)
import           Data.FingerTree         (FingerTree, Measured (..))
import qualified Data.FingerTree         as FT
import           Data.Function           (on)
import           Data.Semigroup.Generic  (GenericSemigroupMonoid (..))
import           Data.Set                (Set)
import qualified Data.Set                as Set
import           GHC.Generics            (Generic)
import           Ledger                  (TxIn (txInRef), TxOutRef (..))
import           Plutus.ChainIndex.Tx    (ChainIndexTx (..), citxInputs, txOutsWithRef)
import           Plutus.ChainIndex.Types (Tip (..))
import           Prettyprinter           (Pretty (..), (<+>))

-- | The effect of a transaction (or a number of them) on the utxo set.
data TxUtxoBalance =
    TxUtxoBalance
        { _tubUnspentOutputs       :: Set TxOutRef -- ^ Outputs newly added by the transaction(s)
        , _tubUnmatchedSpentInputs :: Set TxOutRef -- ^ Outputs spent by the transaction(s)
        }
        deriving stock (Eq, Show, Generic)
        deriving anyclass (FromJSON, ToJSON)

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
        , _usTip           :: Tip -- ^ Tip of our chain sync client
        }
        deriving stock (Eq, Show, Generic)
        deriving (Semigroup, Monoid) via (GenericSemigroupMonoid UtxoState)
        deriving anyclass (FromJSON, ToJSON)

makeLenses ''UtxoState

fromTx :: ChainIndexTx -> TxUtxoBalance
fromTx tx =
    TxUtxoBalance
        { _tubUnspentOutputs = Set.fromList $ fmap snd $ txOutsWithRef tx
        , _tubUnmatchedSpentInputs = Set.mapMonotonic txInRef (view citxInputs tx)
        }

type UtxoIndex = FingerTree UtxoState UtxoState
instance Measured UtxoState UtxoState where
    measure = id

utxoState :: UtxoIndex -> UtxoState
utxoState = measure

-- | Whether a 'TxOutRef' is a member of the UTXO set (ie. unspent)
isUnspentOutput :: TxOutRef -> UtxoState -> Bool
isUnspentOutput r = Set.member r . view (usTxUtxoBalance . tubUnspentOutputs)

tip :: UtxoState -> Tip
tip = view usTip

instance Ord UtxoState where
    compare = compare `on` tip

-- | The UTXO set
unspentOutputs :: UtxoState -> Set TxOutRef
unspentOutputs = view (usTxUtxoBalance . tubUnspentOutputs)

-- | 'UtxoIndex' for a single block
fromBlock :: Tip -> [ChainIndexTx] -> UtxoState
fromBlock tip_ transactions =
    UtxoState
            { _usTxUtxoBalance = foldMap fromTx transactions
            , _usTip           = tip_
            }

-- | Outcome of inserting a 'UtxoState' into the utxo index
data InsertUtxoPosition =
    InsertAtEnd -- ^ The utxo state was added to the end. Returns the new index
    | InsertBeforeEnd -- ^ The utxo state was added somewhere before the end. Returns the new index and the tip
    deriving stock (Eq, Ord, Show, Generic)
    deriving anyclass (FromJSON, ToJSON)

instance Pretty InsertUtxoPosition where
  pretty = \case
    InsertAtEnd     -> "UTxO state was added to the end."
    InsertBeforeEnd -> "UTxO state was added somewhere before the end."

data InsertUtxoSuccess =
    InsertUtxoSuccess
        { newIndex       :: UtxoIndex
        , insertPosition :: InsertUtxoPosition
        }

instance Pretty InsertUtxoSuccess where
  pretty = \case
    InsertUtxoSuccess _ insertPosition -> pretty insertPosition

-- | UTXO state could not be inserted into the chain index
data InsertUtxoFailed =
    DuplicateBlock Tip -- ^ Insertion failed as there was already a block with the given number
    | InsertUtxoNoTip -- ^ The '_usTip' field of the argument was 'Last Nothing'
    deriving stock (Eq, Ord, Show, Generic)
    deriving anyclass (FromJSON, ToJSON)

instance Pretty InsertUtxoFailed where
  pretty = \case
    DuplicateBlock _ -> "UTxO insertion failed - already a block with the given number"
    InsertUtxoNoTip  -> "UTxO insertion failed - no tip"

-- | Insert a 'UtxoState' into the index
insert :: UtxoState -> UtxoIndex -> Either InsertUtxoFailed InsertUtxoSuccess
insert   UtxoState{_usTip=TipAtGenesis} _ = Left InsertUtxoNoTip
insert s@UtxoState{_usTip=thisTip} ix =
    let (before, after) = FT.split (s <=)  ix
    in case tip (measure after) of
        TipAtGenesis -> Right $ InsertUtxoSuccess{newIndex = before FT.|> s, insertPosition = InsertAtEnd}
        t | t > thisTip -> Right $ InsertUtxoSuccess{newIndex = (before FT.|> s) <> after, insertPosition = InsertBeforeEnd}
          | otherwise   -> Left  $ DuplicateBlock t

-- | Reason why the 'rollback' operation failed
data RollbackFailed =
    RollbackNoTip  -- ^ Rollback failed because the utxo index had no tip (not synchronised)
    | TipMismatch { foundTip :: Tip, targetTip :: Tip } -- ^ Unable to roll back to 'expectedTip' because the tip at that position was different
    | OldTipNotFound Tip -- ^ Unable to find the old tip
    deriving stock (Eq, Ord, Show, Generic)
    deriving anyclass (FromJSON, ToJSON)

instance Pretty RollbackFailed where
  pretty = \case
    RollbackNoTip -> "UTxO index had no tip (not synchronised)"
    TipMismatch foundTip targetTip ->
          "Unable to rollback to"
      <+> pretty targetTip
      <+> "because the tip at that position"
      <+> pretty foundTip
      <+> "was different"
    OldTipNotFound t -> "Unable to find the old tip" <+> pretty t

data RollbackResult =
    RollbackResult
        { newTip          :: Tip
        , rolledBackIndex :: UtxoIndex
        }

viewTip :: UtxoIndex -> Tip
viewTip = tip . measure

-- | Perform a rollback on the utxo index
rollback :: Tip -> UtxoIndex -> Either RollbackFailed RollbackResult
rollback _             (viewTip -> TipAtGenesis) = Left RollbackNoTip
rollback targetTip idx@(viewTip -> currentTip)
    -- The rollback happened sometime after the current tip.
    | currentTip < targetTip = Left TipMismatch{foundTip=currentTip, targetTip}
    | otherwise = do
        let (before, _) = FT.split ((> targetTip) . tip) idx

        case tip (measure before) of
            TipAtGenesis -> Left $ OldTipNotFound targetTip
            oldTip | oldTip == targetTip -> Right RollbackResult{newTip=oldTip, rolledBackIndex=before}
                   | otherwise           -> Left  TipMismatch{foundTip=oldTip, targetTip}
