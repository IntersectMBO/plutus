{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds     #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE DeriveAnyClass      #-}
{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE DerivingVia         #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE MonoLocalBinds      #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}
module Language.Plutus.Contract.Effects.AwaitTxConfirmed where

import           Data.Aeson                       (FromJSON, ToJSON)
import           Data.Row
import           Data.Text.Prettyprint.Doc
import           GHC.Generics                     (Generic)
import           Ledger                           (TxId)

import           Language.Plutus.Contract.Request (ContractRow, requestMaybe)
import           Language.Plutus.Contract.Schema  (Event (..), Handlers (..), Input, Output)
import           Language.Plutus.Contract.Types   (AsContractError, Contract)

type TxConfirmationSym = "tx-confirmation"

type HasTxConfirmation s =
    ( HasType TxConfirmationSym TxConfirmed (Input s)
    , HasType TxConfirmationSym TxId (Output s)
    , ContractRow s)

newtype TxConfirmed =
    TxConfirmed { unTxConfirmed :: TxId }
        deriving stock (Eq, Ord, Generic, Show)
        deriving anyclass (ToJSON, FromJSON)
        deriving Pretty via TxId

type TxConfirmation = TxConfirmationSym .== (TxConfirmed, TxId)

-- TODO: Configurable level of confirmation (for example, as soon as the tx is
--       included in a block, or only when it can't be rolled back anymore)
-- | Wait until a transaction is confirmed (added to the ledger).
awaitTxConfirmed :: forall w s e. (AsContractError e, HasTxConfirmation s) => TxId -> Contract w s e ()
awaitTxConfirmed i =
    let check :: TxConfirmed -> Maybe ()
        check (TxConfirmed txId') =
            if txId' == i then Just () else Nothing
    in
    requestMaybe @w @TxConfirmationSym @_ @_ @s i check

event
    :: forall s.
    ( HasTxConfirmation s )
    => TxId
    -> Event s
event = Event . IsJust (Label @TxConfirmationSym) . TxConfirmed

txId
    :: forall s.
    ( HasTxConfirmation s )
    => Handlers s
    -> Maybe TxId
txId (Handlers r) = trial' r (Label @TxConfirmationSym)
