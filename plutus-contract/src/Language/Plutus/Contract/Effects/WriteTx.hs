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
import           Language.Plutus.Contract.Schema  (Event (..), First, Hooks (..), Second)
import           Language.Plutus.Contract.Tx      (UnbalancedTx)

type HasWriteTx s =
    ( HasType "tx" () (First s)
    , HasType "tx" PendingTransactions (Second s)
    , ContractRow s)

type WriteTx = "tx" .== ((), PendingTransactions)

newtype PendingTransactions =
  PendingTransactions { unPendingTransactions :: [UnbalancedTx] }
    deriving stock (Eq, Generic, Show)
    deriving newtype (Semigroup, Monoid, ToJSON, FromJSON)

--  | Send an unbalanced transaction to the wallet.
writeTx :: forall s. HasWriteTx s => UnbalancedTx -> Contract s ()
writeTx t = request @"tx" @_ @_ @s (PendingTransactions [t])

event
  :: forall s. (HasType "tx" () (First s), AllUniqueLabels (First s))
  => Event s
event = Event (IsJust #tx ())

transactions
  :: forall s. ( HasType "tx" PendingTransactions (Second s) )
   => Hooks s
   -> [UnbalancedTx]
transactions (Hooks r) = unPendingTransactions $ r .! #tx
