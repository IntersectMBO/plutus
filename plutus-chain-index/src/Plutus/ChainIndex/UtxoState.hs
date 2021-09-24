{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE DerivingStrategies    #-}
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
    , viewTip
    ) where

import           Codec.Serialise                   (Serialise)
import           Control.Lens                      (makeLenses, view)
import           Data.Aeson                        (FromJSON, ToJSON)
import           Data.FingerTree                   (FingerTree, Measured (..))
import qualified Data.FingerTree                   as FT
import           Data.Function                     (on)
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

type UtxoIndex a = FingerTree (UtxoState a) (UtxoState a)
instance Monoid a => Measured (UtxoState a) (UtxoState a) where
    measure = id

utxoState :: Measured (UtxoState a) (UtxoState a)
          => UtxoIndex a
          -> UtxoState a
utxoState = measure

-- | Whether a 'TxOutRef' is a member of the UTXO set (ie. unspent)
isUnspentOutput :: TxOutRef -> UtxoState TxUtxoBalance -> Bool
isUnspentOutput r = Set.member r . view (usTxUtxoData . tubUnspentOutputs)

tip :: UtxoState a -> Tip
tip = view usTip

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
       ( Measured (UtxoState a) (UtxoState a)
       , Eq a
       )
       => UtxoState a
       -> FingerTree (UtxoState a) (UtxoState a)
       -> Either InsertUtxoFailed (InsertUtxoSuccess a)
insert   UtxoState{_usTip=TipAtGenesis} _ = Left InsertUtxoNoTip
insert s@UtxoState{_usTip=thisTip} ix =
    let (before, after) = FT.split (s <=)  ix
    in case tip (measure after) of
        TipAtGenesis -> Right $ InsertUtxoSuccess{newIndex = before FT.|> s, insertPosition = InsertAtEnd}
        t | t > thisTip -> Right $ InsertUtxoSuccess{newIndex = (before FT.|> s) <> after, insertPosition = InsertBeforeEnd}
          | otherwise   -> Left  $ DuplicateBlock t

data RollbackResult a =
    RollbackResult
        { newTip          :: Tip
        , rolledBackIndex :: UtxoIndex a
        }

viewTip :: Measured (UtxoState a) (UtxoState a)
        => UtxoIndex a
        -> Tip
viewTip = tip . measure

-- | Perform a rollback on the utxo index
rollback :: Point
         -> UtxoIndex TxUtxoBalance
         -> Either RollbackFailed (RollbackResult TxUtxoBalance)
rollback PointAtGenesis (viewTip -> TipAtGenesis) = Right (RollbackResult TipAtGenesis mempty)
rollback _ (viewTip -> TipAtGenesis) = Left RollbackNoTip
rollback targetPoint idx@(viewTip -> currentTip)
    -- The rollback happened sometime after the current tip.
    | not (targetPoint `pointLessThanTip` currentTip) =
        Left TipMismatch{foundTip=currentTip, targetPoint}
    | otherwise = do
        let (before, _) = FT.split (pointLessThanTip targetPoint . tip) idx

        case tip (measure before) of
            TipAtGenesis -> Left $ OldPointNotFound targetPoint
            oldTip | targetPoint `pointsToTip` oldTip ->
                       Right RollbackResult{newTip=oldTip, rolledBackIndex=before}
                   | otherwise                        ->
                       Left  TipMismatch{foundTip=oldTip, targetPoint=targetPoint}
    where
      pointLessThanTip :: Point -> Tip -> Bool
      pointLessThanTip PointAtGenesis  _               = True
      pointLessThanTip (Point pSlot _) (Tip tSlot _ _) = pSlot < tSlot
      pointLessThanTip _               TipAtGenesis    = False
