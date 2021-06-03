{-# LANGUAGE ConstraintKinds  #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MonoLocalBinds   #-}
{-# LANGUAGE TypeOperators    #-}
module Plutus.Contract(
      Contract(..)
    , ContractError(..)
    , AsContractError(..)
    , HasBlockchainActions
    , BlockchainActions
    , both
    , selectEither
    , select
    , (>>)
    , throwError
    , handleError
    , mapError
    , runError
    -- * Dealing with time
    , HasAwaitSlot
    , AwaitSlot
    , awaitSlot
    , currentSlot
    , waitNSlots
    , until
    , when
    , timeout
    , between
    , collectUntil
    -- * Endpoints
    , HasEndpoint
    , EndpointDescription(..)
    , Endpoint
    , endpoint
    , endpointWithMeta
    -- * Blockchain events
    , HasWatchAddress
    , WatchAddress
    , AddressChangeRequest(..)
    , AddressChangeResponse(..)
    , addressChangeRequest
    , nextTransactionsAt
    , watchAddressUntil
    , fundsAtAddressGt
    , fundsAtAddressGeq
    -- * UTXO set
    , HasUtxoAt
    , UtxoAt
    , utxoAt
    -- * Wallet's own public key
    , HasOwnPubKey
    , OwnPubKey
    , ownPubKey
    -- * Contract instance Id
    , HasOwnId
    , ContractInstanceId
    , ownInstanceId
    -- * Notifications
    , tell
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
    -- * Logging
    , logDebug
    , logInfo
    , logWarn
    , logError
    -- * Row-related things
    , HasType
    , ContractRow
    , type (.\/)
    , type Empty
    ) where

import           Data.Aeson                               (ToJSON (toJSON))
import           Data.Row

import           Plutus.Contract.Effects.AwaitSlot        as AwaitSlot
import           Plutus.Contract.Effects.AwaitTxConfirmed as AwaitTxConfirmed
import           Plutus.Contract.Effects.ExposeEndpoint
import           Plutus.Contract.Effects.Instance
import           Plutus.Contract.Effects.OwnPubKey        as OwnPubKey
import           Plutus.Contract.Effects.UtxoAt           as UtxoAt
import           Plutus.Contract.Effects.WatchAddress     as WatchAddress
import           Plutus.Contract.Effects.WriteTx

import           Plutus.Contract.Request                  (ContractRow)
import           Plutus.Contract.Typed.Tx                 as Tx
import           Plutus.Contract.Types                    (AsCheckpointError (..), AsContractError (..),
                                                           CheckpointError (..), Contract (..), ContractError (..),
                                                           checkpoint, handleError, mapError, runError, select,
                                                           selectEither, throwError)

import qualified Control.Monad.Freer.Extras.Log           as L
import qualified Control.Monad.Freer.Writer               as W
import           Prelude                                  hiding (until)
import           Wallet.API                               (WalletAPIError)

-- | Schema for contracts that can interact with the blockchain (via a node
--   client & signing process)
type BlockchainActions =
  AwaitSlot
  .\/ WatchAddress
  .\/ WriteTx
  .\/ UtxoAt
  .\/ OwnPubKey
  .\/ TxConfirmation
  .\/ OwnId

type HasBlockchainActions s =
  ( HasAwaitSlot s
  , HasWatchAddress s
  , HasWriteTx s
  , HasUtxoAt s
  , HasOwnPubKey s
  , HasTxConfirmation s
  , HasOwnId s
  )

-- | Execute both contracts in any order
both :: Contract w s e a -> Contract w s e b -> Contract w s e (a, b)
both a b =
  let swap (b_, a_) = (a_, b_) in
  ((,) <$> a <*> b) `select` (fmap swap ((,) <$> b <*> a))

-- | Log a message at the 'Debug' level
logDebug :: ToJSON a => a -> Contract w s e ()
logDebug = Contract . L.logDebug . toJSON

-- | Log a message at the 'Info' level
logInfo :: ToJSON a => a -> Contract w s e ()
logInfo = Contract . L.logInfo . toJSON

-- | Log a message at the 'Warning' level
logWarn :: ToJSON a => a -> Contract w s e ()
logWarn = Contract . L.logWarn . toJSON

-- | Log a message at the 'Error' level
logError :: ToJSON a => a -> Contract w s e ()
logError = Contract . L.logError . toJSON

-- | Update the contract's accumulating state @w@
tell :: w -> Contract w s e ()
tell = Contract . W.tell

