{-# LANGUAGE ConstraintKinds  #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MonoLocalBinds   #-}
{-# LANGUAGE TypeOperators    #-}
module Language.Plutus.Contract(
      Contract(..)
    , ContractError(..)
    , AsContractError(..)
    , HasBlockchainActions
    , BlockchainActions
    , both
    , selectEither
    , select
    , (>>)
    , (<|>)
    , checkpoint
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
    , WalletAPIError
    , writeTx
    , writeTxSuccess
    -- * Blockchain events
    , HasWatchAddress
    , WatchAddress
    , nextTransactionAt
    , watchAddressUntil
    , fundsAtAddressGt
    , awaitTransactionConfirmed
    -- * UTXO set
    , HasUtxoAt
    , utxoAt
    -- * Transactions
    , module Tx
    -- * Row-related things
    , HasType
    , ContractRow
    , type (.\/)
    , type Empty
    , waitingForBlockchainActions
    ) where

import           Control.Applicative                             (Alternative (..))
import           Data.Row

import           Language.Plutus.Contract.Effects.AwaitSlot
import           Language.Plutus.Contract.Effects.ExposeEndpoint
import           Language.Plutus.Contract.Effects.UtxoAt         as UtxoAt
import           Language.Plutus.Contract.Effects.WatchAddress   as WatchAddress
import           Language.Plutus.Contract.Effects.WriteTx
import           Language.Plutus.Contract.Util                   (both, selectEither)

import           Language.Plutus.Contract.Request                (AsContractError (..), Contract (..),
                                                                  ContractError (..), ContractRow, checkpoint, select)
import           Language.Plutus.Contract.Schema                 (Handlers)

import           Language.Plutus.Contract.Tx                     as Tx

import           Prelude                                         hiding (until)
import           Wallet.API                                      (WalletAPIError)

-- | Schema for contracts that can interact with the blockchain (via a node
--   client & signing process)
type BlockchainActions =
  AwaitSlot
  .\/ WatchAddress
  .\/ WriteTx
  .\/ UtxoAt

type HasBlockchainActions s =
  ( HasAwaitSlot s
  , HasWatchAddress s
  , HasWriteTx s
  , HasUtxoAt s
  )

-- | Check if there are handlers for any of the four blockchain
--   events.
waitingForBlockchainActions
  :: ( HasWriteTx s, HasUtxoAt s )
  => Handlers s
  -> Bool
waitingForBlockchainActions handlers =
  UtxoAt.addresses handlers /= mempty
  || transactions handlers /= mempty
