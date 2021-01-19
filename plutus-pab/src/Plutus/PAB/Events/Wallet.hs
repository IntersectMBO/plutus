{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE LambdaCase         #-}
{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE StrictData         #-}

module Plutus.PAB.Events.Wallet where

import           Data.Aeson                (FromJSON, ToJSON)
import           Data.Text.Prettyprint.Doc
import           GHC.Generics              (Generic)
import           Ledger                    (Tx, txId)

newtype WalletEvent =
    BalancedTx Tx
    deriving (Show, Eq, Generic)
    deriving newtype (FromJSON, ToJSON)

instance Pretty WalletEvent where
    pretty = \case
        BalancedTx tx -> "BalancedTx:" <+> pretty (txId tx)
