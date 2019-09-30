{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds     #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE DerivingStrategies  #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE MonoLocalBinds      #-}
{-# LANGUAGE OverloadedLabels    #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}
module Language.Plutus.Contract.Effects.WriteTx where

import           Data.Aeson                       (FromJSON, ToJSON)
import           Data.Row
import           GHC.Generics                     (Generic)

import           Language.Plutus.Contract.Request as Req
import           Language.Plutus.Contract.Schema  (Event (..), Handlers (..), Input, Output)
import           Language.Plutus.Contract.Tx      (UnbalancedTx)

type TxSymbol = "tx"

type HasWriteTx s =
    ( HasType TxSymbol () (Input s)
    , HasType TxSymbol PendingTransactions (Output s)
    , ContractRow s)

type WriteTx = TxSymbol .== ((), PendingTransactions)

newtype PendingTransactions =
  PendingTransactions { unPendingTransactions :: [UnbalancedTx] }
    deriving stock (Eq, Generic, Show)
    deriving newtype (Semigroup, Monoid, ToJSON, FromJSON)

--  | Send an unbalanced transaction to the wallet.
writeTx :: forall s. HasWriteTx s => UnbalancedTx -> Contract s ()
writeTx t = request @TxSymbol @_ @_ @s (PendingTransactions [t])

event
  :: forall s. (HasType TxSymbol () (Input s), AllUniqueLabels (Input s))
  => Event s
event = Event (IsJust #tx ())

transactions
  :: forall s. ( HasType TxSymbol PendingTransactions (Output s) )
   => Handlers s
   -> [UnbalancedTx]
transactions (Handlers r) = unPendingTransactions $ r .! #tx
