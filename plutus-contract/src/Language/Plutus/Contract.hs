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
    , withContractError
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
    -- * Row-related things
    , HasType
    , ContractRow
    , type (.\/)
    , type Empty
    , waitingForBlockchainActions
    ) where

import           Control.Applicative                               (Alternative (..))
import           Data.Row

import           Language.Plutus.Contract.Effects.AwaitSlot
import           Language.Plutus.Contract.Effects.AwaitTxConfirmed
import           Language.Plutus.Contract.Effects.ExposeEndpoint
import           Language.Plutus.Contract.Effects.OwnPubKey        as OwnPubKey
import           Language.Plutus.Contract.Effects.UtxoAt           as UtxoAt
import           Language.Plutus.Contract.Effects.WatchAddress     as WatchAddress
import           Language.Plutus.Contract.Effects.WriteTx
import           Language.Plutus.Contract.Util                     (both, selectEither)

import           Language.Plutus.Contract.Request                  (AsContractError (..), Contract (..),
                                                                    ContractError (..), ContractRow, checkpoint, select,
                                                                    withContractError)
import           Language.Plutus.Contract.Schema                   (Handlers)
import           Language.Plutus.Contract.Typed.Tx                 as Tx

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
  UtxoAt.addresses handlers /= mempty
  || transactions handlers /= mempty
  || OwnPubKey.request handlers /= mempty
