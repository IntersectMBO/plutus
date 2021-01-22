{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE LambdaCase         #-}
{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE StrictData         #-}

module Plutus.PAB.Events.Node
    ( NodeEvent(..)
    ) where

import           Data.Aeson                (FromJSON, ToJSON)
import           Data.Text.Prettyprint.Doc
import           GHC.Generics              (Generic)

import           Ledger                    (Tx)

newtype NodeEvent
    = SubmittedTx Tx
  -- ^ Confirmation that the transactions were received.
  -- TODO: Rollbacks?
  -- | Rollback Int -- ^ n blocks were rolled back
    deriving (Show, Eq, Generic)
    deriving newtype (FromJSON, ToJSON)

instance Pretty NodeEvent where
  pretty = \case
    SubmittedTx tx -> "SubmittedTx:" <+> pretty tx
