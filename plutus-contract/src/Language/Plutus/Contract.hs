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
    , mapError
    , throwError
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
    -- * Blockchain events
    , HasWatchAddress
    , WatchAddress
    , nextTransactionAt
    , watchAddressUntil
    , fundsAtAddressGt
    , fundsAtAddressGeq
    , awaitTransactionConfirmed
    -- * UTXO set
    , HasUtxoAt
    , UtxoAt
    , utxoAt
    -- * Wallet's own public key
    , HasOwnPubKey
    , OwnPubKey
    , ownPubKey
    -- * Transactions
    , HasWriteTx
    , WriteTx
    , WalletAPIError
    , submitTx
    , submitTxConfirmed
    , submitTxConstraints
    , submitTxConstraintsSpending
    , submitTxConstraintsWith
    , submitUnbalancedTx
    -- ** Creating transactions
    , module Tx
    -- ** Tx confirmation
    , HasTxConfirmation
    , TxConfirmation
    , awaitTxConfirmed
    -- * Checkpoints
    , checkpoint
    , AsCheckpointError(..)
    , CheckpointError(..)
    -- * Row-related things
    , HasType
    , ContractRow
    , type (.\/)
    , type Empty
    , waitingForBlockchainActions
    ) where

import           Data.Maybe                                        (isJust)
import           Data.Row

import           Language.Plutus.Contract.Effects.AwaitSlot
import           Language.Plutus.Contract.Effects.AwaitTxConfirmed
import           Language.Plutus.Contract.Effects.ExposeEndpoint
import           Language.Plutus.Contract.Effects.OwnPubKey        as OwnPubKey
import           Language.Plutus.Contract.Effects.UtxoAt           as UtxoAt
import           Language.Plutus.Contract.Effects.WatchAddress     as WatchAddress
import           Language.Plutus.Contract.Effects.WriteTx
import           Language.Plutus.Contract.Util                     (both)

import           Language.Plutus.Contract.Request                  (ContractRow)
import           Language.Plutus.Contract.Schema                   (Handlers)
import           Language.Plutus.Contract.Typed.Tx                 as Tx
import           Language.Plutus.Contract.Types                    (AsCheckpointError (..), AsContractError (..),
                                                                    CheckpointError (..), Contract (..),
                                                                    ContractError (..), checkpoint, mapError, select,
                                                                    selectEither, throwError)

import           Prelude                                           hiding (until)
import           Wallet.API                                        (WalletAPIError)

-- | Schema for contracts that can interact with the blockchain (via a node
--   client & signing process)
type BlockchainActions =
  AwaitSlot
  .\/ WatchAddress
  .\/ WriteTx
  .\/ UtxoAt
  .\/ OwnPubKey
  .\/ TxConfirmation

type HasBlockchainActions s =
  ( HasAwaitSlot s
  , HasWatchAddress s
  , HasWriteTx s
  , HasUtxoAt s
  , HasOwnPubKey s
  , HasTxConfirmation s
  )

-- | Check if there are handlers for any of the four blockchain
--   events.
waitingForBlockchainActions
  :: ( HasWriteTx s, HasUtxoAt s, HasOwnPubKey s )
  => Handlers s
  -> Bool
waitingForBlockchainActions handlers =
  isJust (UtxoAt.utxoAtRequest handlers)
  || isJust (pendingTransaction handlers)
  || isJust (OwnPubKey.request handlers)
