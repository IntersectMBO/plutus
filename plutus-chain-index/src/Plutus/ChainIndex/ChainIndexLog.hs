{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE LambdaCase         #-}
{-# LANGUAGE OverloadedStrings  #-}
module Plutus.ChainIndex.ChainIndexLog (ChainIndexLog(..), InsertUtxoPosition(..)) where

import           Cardano.BM.Data.Tracer            (ToObject (..))
import           Control.Monad.Freer.Extras.Beam   (BeamLog)
import           Data.Aeson                        (FromJSON, ToJSON)
import           GHC.Generics                      (Generic)
import           Ledger                            (TxId, TxOut, TxOutRef)
import           Plutus.ChainIndex.ChainIndexError (ChainIndexError)
import           Plutus.ChainIndex.Types           (Tip (..))
import           Plutus.Contract.CardanoAPI        (FromCardanoError (..))
import           Prettyprinter                     (Pretty (..), colon, (<+>))

data ChainIndexLog =
    InsertionSuccess Tip InsertUtxoPosition
    | ConversionFailed FromCardanoError
    | RollbackSuccess Tip
    | Err ChainIndexError
    | TxNotFound TxId
    | TxOutNotFound TxOutRef
    | TipIsGenesis
    | NoDatumScriptAddr TxOut
    | BeamLogItem BeamLog
    deriving stock (Eq, Show, Generic)
    deriving anyclass (FromJSON, ToJSON, ToObject)

instance Pretty ChainIndexLog where
  pretty = \case
    InsertionSuccess t p ->
         "InsertionSuccess"
      <> colon
      <+> "New tip is"
      <+> pretty t
      <> "."
      <+> pretty p
    RollbackSuccess t -> "RollbackSuccess: New tip is" <+> pretty t
    ConversionFailed cvError -> "Conversion failed: " <+> pretty cvError
    Err ciError -> "ChainIndexError:" <+> pretty ciError
    TxNotFound txid -> "TxNotFound:" <+> pretty txid
    TxOutNotFound ref -> "TxOut not found with:" <+> pretty ref
    TipIsGenesis -> "TipIsGenesis"
    NoDatumScriptAddr txout -> "The following transaction output from a script adress does not have a datum:" <+> pretty txout
    BeamLogItem b -> "BeamLogItem:" <+> pretty b

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
