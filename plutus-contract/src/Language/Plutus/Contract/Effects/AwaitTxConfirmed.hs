{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds     #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE DeriveAnyClass      #-}
{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE DerivingStrategies  #-}
{-# LANGUAGE DerivingVia         #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE MonoLocalBinds      #-}
{-# LANGUAGE NamedFieldPuns      #-}
{-# LANGUAGE OverloadedLabels    #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}
module Language.Plutus.Contract.Effects.AwaitTxConfirmed where

import           Data.Aeson                       (FromJSON, ToJSON)
import           Data.Row
import           Data.Set                         (Set)
import qualified Data.Set                         as Set
import           Data.Text.Prettyprint.Doc
import           Data.Text.Prettyprint.Doc.Extras
import           GHC.Generics                     (Generic)
import           Ledger                           (TxId)

import           IOTS                             (IotsType)
import           Language.Plutus.Contract.Request (Contract, ContractRow, requestMaybe)
import           Language.Plutus.Contract.Schema  (Event (..), Handlers (..), Input, Output)

type TxConfirmationSym = "tx-confirmation"

type HasTxConfirmation s =
    ( HasType TxConfirmationSym TxConfirmed (Input s)
    , HasType TxConfirmationSym TxIdSet (Output s)
    , ContractRow s)

newtype TxConfirmed =
    TxConfirmed { unTxConfirmed :: TxId }
        deriving stock (Eq, Ord, Generic, Show)
        deriving newtype (ToJSON, FromJSON)
        deriving anyclass IotsType
        deriving Pretty via TxId

newtype TxIdSet =
    TxIdSet { unTxIdSet :: Set TxId }
        deriving stock (Eq, Ord, Generic, Show)
        deriving newtype (Semigroup, Monoid, ToJSON, FromJSON)
        deriving anyclass IotsType
        deriving Pretty via (PrettyFoldable Set TxId)

type TxConfirmation = TxConfirmationSym .== (TxConfirmed, TxIdSet)

-- TODO: Configurable level of confirmation (for example, as soon as the tx is
--       included in a block, or only when it can't be rolled back anymore)
-- | Wait until a transaction is confirmed (added to the ledger).
awaitTxConfirmed :: forall s e. HasTxConfirmation s => TxId -> Contract s e ()
awaitTxConfirmed txId =
    let check :: TxConfirmed -> Maybe ()
        check (TxConfirmed txId') =
            if txId' == txId then Just () else Nothing
    in
    requestMaybe @TxConfirmationSym @_ @_ @s (TxIdSet $ Set.singleton txId) check

event
    :: forall s.
    ( HasTxConfirmation s )
    => TxId
    -> Event s
event = Event . IsJust (Label @TxConfirmationSym) . TxConfirmed

txIds
    :: forall s.
    ( HasTxConfirmation s )
    => Handlers s
    -> Set TxId
txIds (Handlers r) = unTxIdSet (r .! Label @TxConfirmationSym)
