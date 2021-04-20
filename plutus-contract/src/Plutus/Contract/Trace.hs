{-# LANGUAGE AllowAmbiguousTypes    #-}
{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE DeriveAnyClass         #-}
{-# LANGUAGE DeriveGeneric          #-}
{-# LANGUAGE DerivingStrategies     #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE KindSignatures         #-}
{-# LANGUAGE LambdaCase             #-}
{-# LANGUAGE MonoLocalBinds         #-}
{-# LANGUAGE NamedFieldPuns         #-}
{-# LANGUAGE NumericUnderscores     #-}
{-# LANGUAGE OverloadedStrings      #-}
{-# LANGUAGE RankNTypes             #-}
{-# LANGUAGE TemplateHaskell        #-}
{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE TypeOperators          #-}
-- | A trace is a sequence of actions by simulated wallets that can be run
--   on the mockchain. This module contains the functions needed to build
--   traces.
module Plutus.Contract.Trace
    ( TraceError(..)
    , EndpointError(..)
    , AsTraceError(..)
    , toNotifyError
    -- * Running 'ContractTrace' actions
    -- * Constructing 'ContractTrace' actions
    , handleUtxoQueries
    , handleAddressChangedAtQueries
    -- * Handle blockchain events repeatedly
    , handleBlockchainQueries
    , handleSlotNotifications
    -- * Initial distributions of emulated chains
    , InitialDistribution
    , defaultDist
    , defaultDistFor
    -- * Wallets
    , EM.Wallet(..)
    , EM.walletPubKey
    , EM.walletPrivKey
    , allWallets
    , makeTimed
    ) where

import           Control.Arrow                            ((>>>), (>>^))
import           Control.Lens                             (from, makeClassyPrisms, review, view)
import           Control.Monad.Freer
import           Control.Monad.Freer.Extras.Log           (LogMessage, LogMsg, LogObserve)
import           Control.Monad.Freer.Reader               (Reader)
import           Control.Monad.Freer.State                (State, gets)
import qualified Data.Aeson.Types                         as JSON
import           Data.Map                                 (Map)
import qualified Data.Map                                 as Map
import           Data.Text.Prettyprint.Doc                (Pretty, pretty, (<+>))
import           GHC.Generics                             (Generic)

import           Data.Text                                (Text)
import           Plutus.Contract                          (HasAwaitSlot, HasTxConfirmation, HasUtxoAt, HasWatchAddress,
                                                           HasWriteTx)
import           Plutus.Contract.Schema                   (Event (..), Handlers (..))

import qualified Plutus.Contract.Effects.AwaitSlot        as AwaitSlot
import           Plutus.Contract.Effects.AwaitTxConfirmed (TxConfirmed (..))
import qualified Plutus.Contract.Effects.AwaitTxConfirmed as AwaitTxConfirmed
import           Plutus.Contract.Effects.Instance         (HasOwnId)
import qualified Plutus.Contract.Effects.Instance         as OwnInstance
import           Plutus.Contract.Effects.Notify           (HasContractNotify)
import qualified Plutus.Contract.Effects.Notify           as Notify
import           Plutus.Contract.Effects.OwnPubKey        (HasOwnPubKey)
import qualified Plutus.Contract.Effects.OwnPubKey        as OwnPubKey
import qualified Plutus.Contract.Effects.UtxoAt           as UtxoAt
import qualified Plutus.Contract.Effects.WatchAddress     as WatchAddress
import qualified Plutus.Contract.Effects.WriteTx          as WriteTx
import           Plutus.Contract.Trace.RequestHandler     (RequestHandler (..), RequestHandlerLogMsg, maybeToHandler)
import qualified Plutus.Contract.Trace.RequestHandler     as RequestHandler

import qualified Ledger.Ada                               as Ada
import           Ledger.Value                             (Value)

import           Plutus.Trace.Emulator.Types              (EmulatedWalletEffects)
import           Wallet.API                               (ChainIndexEffect)
import           Wallet.Effects                           (ContractRuntimeEffect, WalletEffect)
import           Wallet.Emulator                          (EmulatorState, Wallet)
import qualified Wallet.Emulator                          as EM
import           Wallet.Emulator.LogMessages              (TxBalanceMsg)
import qualified Wallet.Emulator.MultiAgent               as EM
import           Wallet.Emulator.Notify                   (EmulatorNotifyLogMsg (..))
import           Wallet.Types                             (ContractInstanceId, EndpointDescription (..),
                                                           NotificationError (..))

data EndpointError =
    EndpointNotActive (Maybe Wallet) EndpointDescription
    deriving stock (Eq, Show, Generic)
    deriving anyclass (JSON.ToJSON, JSON.FromJSON)

instance Pretty EndpointError where
    pretty = \case
        EndpointNotActive w e ->
            "Endpoint not active:" <+> pretty w <+> pretty e

toNotifyError :: ContractInstanceId -> EndpointError -> NotificationError
toNotifyError i = \case
    EndpointNotActive _ e       -> EndpointNotAvailable i e

-- | Error produced while running a trace. Either a contract-specific
--   error (of type 'e'), or an 'EM.AssertionError' from the emulator.
data TraceError e =
    TraceAssertionError EM.AssertionError
    | TContractError e
    | HookError EndpointError
    deriving (Eq, Show)

type InitialDistribution = Map Wallet Value

makeTimed :: Member (State EmulatorState) effs => EmulatorNotifyLogMsg -> Eff effs EM.EmulatorEvent
makeTimed e = do
    emulatorTime <- gets (view (EM.chainState . EM.currentSlot))
    pure $ review (EM.emulatorTimeEvent emulatorTime) (EM.NotificationEvent e)

handleSlotNotifications ::
    ( HasAwaitSlot s
    , Member (LogObserve (LogMessage Text)) effs
    , Member (LogMsg RequestHandlerLogMsg) effs
    , Member WalletEffect effs
    )
    => RequestHandler effs (Handlers s) (Event s)
handleSlotNotifications =
    maybeToHandler AwaitSlot.request
    >>> RequestHandler.handleSlotNotifications
    >>^ AwaitSlot.event

handleBlockchainQueries ::
    ( HasWriteTx s
    , HasUtxoAt s
    , HasTxConfirmation s
    , HasOwnPubKey s
    , HasWatchAddress s
    , HasOwnId s
    , HasContractNotify s
    , HasAwaitSlot s
    )
    => RequestHandler (Reader ContractInstanceId ': ContractRuntimeEffect ': EmulatedWalletEffects) (Handlers s) (Event s)
handleBlockchainQueries =
    handlePendingTransactions
    <> handleUtxoQueries
    <> handleTxConfirmedQueries
    <> handleOwnPubKeyQueries
    <> handleAddressChangedAtQueries
    <> handleOwnInstanceIdQueries
    <> handleContractNotifications
    <> handleSlotNotifications

-- | Submit the wallet's pending transactions to the blockchain
--   and inform all wallets about new transactions and respond to
--   UTXO queries
handlePendingTransactions ::
    ( HasWriteTx s
    , Member (LogObserve (LogMessage Text)) effs
    , Member (LogMsg RequestHandlerLogMsg) effs
    , Member WalletEffect effs
    , Member ChainIndexEffect effs
    , Member (LogMsg TxBalanceMsg) effs
    )
    => RequestHandler effs (Handlers s) (Event s)
handlePendingTransactions =
    maybeToHandler WriteTx.pendingTransaction
    >>> RequestHandler.handlePendingTransactions
    >>^ WriteTx.event . view (from WriteTx.writeTxResponse)

-- | Look at the "utxo-at" requests of the contract and respond to all of them
--   with the current UTXO set at the given address.
handleUtxoQueries ::
    ( HasUtxoAt s
    , Member (LogObserve (LogMessage Text)) effs
    , Member (LogMsg RequestHandlerLogMsg) effs
    , Member ChainIndexEffect effs
    )
    => RequestHandler effs (Handlers s) (Event s)
handleUtxoQueries =
    maybeToHandler UtxoAt.utxoAtRequest
    >>> RequestHandler.handleUtxoQueries
    >>^ UtxoAt.event

handleTxConfirmedQueries ::
    ( HasTxConfirmation s
    , Member (LogObserve (LogMessage Text)) effs
    , Member ChainIndexEffect effs
    )
    => RequestHandler effs (Handlers s) (Event s)
handleTxConfirmedQueries =
    maybeToHandler AwaitTxConfirmed.txId
    >>> RequestHandler.handleTxConfirmedQueries
    >>^ AwaitTxConfirmed.event . unTxConfirmed

handleAddressChangedAtQueries ::
    ( HasWatchAddress s
    , Member (LogObserve (LogMessage Text)) effs
    , Member (LogMsg RequestHandlerLogMsg) effs
    , Member WalletEffect effs
    , Member ChainIndexEffect effs
    )
    => RequestHandler effs (Handlers s) (Event s)
handleAddressChangedAtQueries =
    maybeToHandler WatchAddress.watchAddressRequest
    >>> RequestHandler.handleAddressChangedAtQueries
    >>^ WatchAddress.event

handleOwnPubKeyQueries ::
    ( HasOwnPubKey s
    , Member (LogObserve (LogMessage Text)) effs
    , Member WalletEffect effs
    )
    => RequestHandler effs (Handlers s) (Event s)
handleOwnPubKeyQueries =
    maybeToHandler OwnPubKey.request
    >>> RequestHandler.handleOwnPubKey
    >>^ OwnPubKey.event

handleOwnInstanceIdQueries ::
    ( HasOwnId s
    , Member (LogObserve (LogMessage Text)) effs
    , Member (Reader ContractInstanceId) effs
    )
    => RequestHandler effs (Handlers s) (Event s)
handleOwnInstanceIdQueries =
    maybeToHandler OwnInstance.request
    >>> RequestHandler.handleOwnInstanceIdQueries
    >>^ OwnInstance.event

handleContractNotifications ::
    ( HasContractNotify s
    , Member (LogObserve (LogMessage Text)) effs
    , Member ContractRuntimeEffect effs
    )
    => RequestHandler effs (Handlers s) (Event s)
handleContractNotifications =
    maybeToHandler Notify.request
    >>> RequestHandler.handleContractNotifications
    >>^ Notify.event

-- | The wallets used in mockchain simulations by default. There are
--   ten wallets because the emulator comes with ten private keys.
allWallets :: [EM.Wallet]
allWallets = EM.Wallet <$> [1 .. 10]

defaultDist :: InitialDistribution
defaultDist = defaultDistFor allWallets

defaultDistFor :: [EM.Wallet] -> InitialDistribution
defaultDistFor wallets = Map.fromList $ zip wallets (repeat (Ada.lovelaceValueOf 100_000_000))

makeClassyPrisms ''TraceError

instance EM.AsAssertionError (TraceError e) where
    _AssertionError = _TraceAssertionError
