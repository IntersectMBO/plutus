{-# LANGUAGE MonoLocalBinds   #-}
{-# LANGUAGE ConstraintKinds  #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators    #-}
module Language.Plutus.Contract(
      Contract
    , HasBlockchainActions
    , BlockchainActions
    , both
    , selectEither
    , select
    , (>>)
    , (<|>)
    -- * Dealing with time
    , HasAwaitSlot
    , AwaitSlot
    , awaitSlot
    , until
    , when
    , timeout
    , between
    , collectUntil
    -- * Endpoints
    , HasEndpoint
    , Endpoint
    , endpoint
    -- * Transactions
    , HasWriteTx
    , WriteTx
    , writeTx
    -- * Blockchain events
    , HasWatchAddress
    , WatchAddress
    , nextTransactionAt
    , watchAddressUntil
    , fundsAtAddressGt
    -- * Transactions
    , module Tx
    -- * Row-related things
    , HasType
    , ContractRow
    , type (.\/)
    , type Empty
    ) where

import           Control.Applicative                             (Alternative(..))
import           Data.Row

import           Language.Plutus.Contract.Effects.AwaitSlot
import           Language.Plutus.Contract.Effects.ExposeEndpoint
import           Language.Plutus.Contract.Effects.WatchAddress
import           Language.Plutus.Contract.Effects.WriteTx
import           Language.Plutus.Contract.Util                   (both, selectEither)

import           Language.Plutus.Contract.Request                (Contract, ContractRow, select)

import           Language.Plutus.Contract.Tx                     as Tx

import           Prelude                                         hiding (until)

-- | Schema for contracts that can interact with the blockchain (via a wallet)
type BlockchainActions =
  AwaitSlot
  .\/ WatchAddress
  .\/ WriteTx

type HasBlockchainActions s =
  ( HasAwaitSlot s
  , HasWatchAddress s
  , HasWriteTx s
  )
