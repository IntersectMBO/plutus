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
    , notifyInstance
    , notify
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

import           Data.Aeson                                        (ToJSON (toJSON))
import           Data.Row                                          hiding (type (.\/))

import           Language.Plutus.Contract.Effects.AwaitSlot        as AwaitSlot
import           Language.Plutus.Contract.Effects.AwaitTxConfirmed as AwaitTxConfirmed
import           Language.Plutus.Contract.Effects.ExposeEndpoint
import           Language.Plutus.Contract.Effects.Instance
import           Language.Plutus.Contract.Effects.Notify
import           Language.Plutus.Contract.Effects.OwnPubKey        as OwnPubKey
import           Language.Plutus.Contract.Effects.UtxoAt           as UtxoAt
import           Language.Plutus.Contract.Effects.WatchAddress     as WatchAddress
import           Language.Plutus.Contract.Effects.WriteTx

import           Data.Row.Extras                                   (type (.\/))
import           Language.Plutus.Contract.Request                  (ContractRow)
import           Language.Plutus.Contract.Typed.Tx                 as Tx
import           Language.Plutus.Contract.Types                    (AsCheckpointError (..), AsContractError (..),
                                                                    CheckpointError (..), Contract (..),
                                                                    ContractError (..), checkpoint, handleError,
                                                                    mapError, runError, select, selectEither,
                                                                    throwError)

import qualified Control.Monad.Freer.Log                           as L
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
  .\/ ContractInstanceNotify
  .\/ OwnId

type HasBlockchainActions s =
  ( HasAwaitSlot s
  , HasWatchAddress s
  , HasWriteTx s
  , HasUtxoAt s
  , HasOwnPubKey s
  , HasTxConfirmation s
  , HasContractNotify s
  , HasOwnId s
  )

-- | Execute both contracts in any order
both :: Contract s e a -> Contract s e b -> Contract s e (a, b)
both a b =
  let swap (b_, a_) = (a_, b_) in
  ((,) <$> a <*> b) `select` (fmap swap ((,) <$> b <*> a))

-- | Log a message at the 'Debug' level
logDebug :: ToJSON a => a -> Contract s e ()
logDebug = Contract . L.logDebug . toJSON

-- | Log a message at the 'Info' level
logInfo :: ToJSON a => a -> Contract s e ()
logInfo = Contract . L.logInfo . toJSON

-- | Log a message at the 'Warning' level
logWarn :: ToJSON a => a -> Contract s e ()
logWarn = Contract . L.logWarn . toJSON

-- | Log a message at the 'Error' level
logError :: ToJSON a => a -> Contract s e ()
logError = Contract . L.logError . toJSON

-- | Send a notification to the outside world. (This is a placeholder
--   until we implement https://jira.iohk.io/browse/SCP-1837)
notify :: ToJSON a => a -> Contract s e ()
notify = logInfo
