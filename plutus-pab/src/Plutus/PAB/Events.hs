{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts   #-}
{-# LANGUAGE LambdaCase         #-}
{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE TemplateHaskell    #-}
{-

Events that we store in the database.

-}
module Plutus.PAB.Events
    ( PABEvent(..)
    , _InstallContract
    , _UpdateContractInstanceState
    , _SubmitTx
    ) where

import           Control.Lens.TH                         (makePrisms)
import           Data.Aeson                              (FromJSON, ToJSON)
import           Data.Text.Prettyprint.Doc               (Pretty, pretty, (<+>))
import           GHC.Generics                            (Generic)
import           Ledger.Tx                               (Tx, txId)
import           Plutus.PAB.Events.Contract              (ContractPABRequest)
import           Plutus.PAB.Events.ContractInstanceState (PartiallyDecodedResponse)
import           Wallet.Types                            (ContractInstanceId)

-- | A structure which ties together all possible event types into one parent.
data PABEvent t =
    InstallContract !t -- ^ Install a contract
    | UpdateContractInstanceState !t !ContractInstanceId !(PartiallyDecodedResponse ContractPABRequest) -- ^ Update the state of a contract instance
    | SubmitTx !Tx -- ^ Send a transaction to the node
    deriving stock (Eq, Show, Generic)
    deriving anyclass (ToJSON, FromJSON)

makePrisms ''PABEvent

instance Pretty t => Pretty (PABEvent t) where
    pretty = \case
        InstallContract t                 -> "Install contract:" <+> pretty t
        UpdateContractInstanceState t i _ -> "Update state:" <+> pretty t <+> pretty i
        SubmitTx t                        -> "SubmitTx:" <+> pretty (txId t)
