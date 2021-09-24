{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE LambdaCase         #-}
{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE RecordWildCards    #-}
module Plutus.ChainIndex.ChainIndexError (ChainIndexError(..), InsertUtxoFailed(..), RollbackFailed(..)) where

import           Data.Aeson              (FromJSON, ToJSON)
import           Data.Text               (Text)
import           GHC.Generics            (Generic)
import           Plutus.ChainIndex.Types (Point (..), Tip (..))
import           Prettyprinter           (Pretty (..), colon, (<+>))

data ChainIndexError =
    InsertionFailed InsertUtxoFailed
    | RollbackFailed RollbackFailed
    | QueryFailedNoTip -- ^ Query failed because the chain index does not have a tip (not synchronised with node)
    | SqlError Text
    deriving stock (Eq, Show, Generic)
    deriving anyclass (FromJSON, ToJSON)

instance Pretty ChainIndexError where
  pretty = \case
    InsertionFailed err -> "Insertion failed" <> colon <+> pretty err
    RollbackFailed err  -> "Rollback failed" <> colon <+> pretty err
    QueryFailedNoTip    -> "Query failed" <> colon <+> "No tip."
    SqlError err        -> pretty err

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

-- | Reason why the 'rollback' operation failed
data RollbackFailed =
    RollbackNoTip  -- ^ Rollback failed because the utxo index had no tip (not synchronised)
    | TipMismatch { foundTip :: Tip, targetPoint :: Point } -- ^ Unable to roll back to 'expectedTip' because the tip at that position was different
    | OldPointNotFound Point -- ^ Unable to find the old tip
    deriving stock (Eq, Ord, Show, Generic)
    deriving anyclass (FromJSON, ToJSON)

instance Pretty RollbackFailed where
  pretty = \case
    RollbackNoTip -> "UTxO index had no tip (not synchronised)"
    TipMismatch{..} ->
          "Unable to rollback to"
      <+> pretty targetPoint
      <+> "because the tip at that position"
      <+> pretty foundTip
      <+> "was different"
    OldPointNotFound t -> "Unable to find the old tip" <+> pretty t
