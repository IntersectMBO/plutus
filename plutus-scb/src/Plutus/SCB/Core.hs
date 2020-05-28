{-# LANGUAGE AllowAmbiguousTypes   #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns        #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Plutus.SCB.Core
    ( dbConnect
    , installContract
    , activateContract
    , reportContractStatus
    , installedContracts
    , activeContracts
    , txHistory
    , activeContractHistory
    , Connection(Connection)
    , ContractCommand(..)
    , invokeContract
    , refreshProjection
    , runCommand
    , runGlobalQuery
    , addProcessBus
    , Source(..)
    , toUUID
    -- * Effects
    , ContractEffects
    , SCBEffects
    -- * Contract messages
    , processAllContractInboxes
    , processAllContractOutboxes
    , callContractEndpoint
    ) where

import           Cardano.Node.RandomTx            (GenRandomTx)
import           Control.Monad                    (void)
import           Control.Monad.Freer              (Eff, Member)
import           Control.Monad.Freer.Error
import           Control.Monad.Freer.Extra.Log
import           Control.Monad.IO.Unlift          (MonadUnliftIO)
import           Control.Monad.Logger             (MonadLogger)
import qualified Control.Monad.Logger             as MonadLogger
import qualified Data.Map.Strict                  as Map
import           Data.Set                         (Set)
import           Data.Text.Prettyprint.Doc        (Pretty, pretty)
import           Database.Persist.Sqlite          (createSqlitePoolFromInfo, mkSqliteConnectionInfo)
import           Eventful.Store.Sql               (defaultSqlEventStoreConfig)
import qualified Ledger
import           Plutus.SCB.Command               (installCommand)
import           Plutus.SCB.Events                (ChainEvent, ContractInstanceId, ContractInstanceState)
import qualified Plutus.SCB.Query                 as Query
import           Plutus.SCB.Types                 (ContractExe, DbConfig (DbConfig), SCBError, Source (..),
                                                   dbConfigFile, dbConfigPoolSize, toUUID)
import           Plutus.SCB.Utils                 (render, tshow)

import           Cardano.Node.Follower            (NodeFollowerEffect)
import           Plutus.SCB.Core.ContractInstance (activateContract, callContractEndpoint, processAllContractInboxes,
                                                   processAllContractOutboxes)
import           Plutus.SCB.Effects.Contract      (ContractCommand (..), ContractEffect, invokeContract)
import           Plutus.SCB.Effects.EventLog      (Connection (..), EventLogEffect, addProcessBus, refreshProjection,
                                                   runCommand, runGlobalQuery)
import qualified Plutus.SCB.Effects.EventLog      as EventLog
import           Plutus.SCB.Effects.UUID          (UUIDEffect)
import           Wallet.API                       (WalletEffect)
import           Wallet.Effects                   (ChainIndexEffect, NodeClientEffect, SigningProcessEffect)

type ContractEffects t =
        '[ EventLogEffect (ChainEvent t)
         , Log
         , UUIDEffect
         , ContractEffect FilePath
         , Error SCBError
         ]

installContract ::
    forall t effs.
    ( Member Log effs
    , Member (EventLogEffect (ChainEvent t)) effs
    , Show t
    )
    => t
    -> Eff effs ()
installContract contractHandle = do
    logInfo $ "Installing: " <> tshow contractHandle
    void $
        runCommand
            installCommand
            UserEventSource
            contractHandle
    logInfo "Installed."

reportContractStatus ::
    forall t effs.
    ( Member Log effs
    , Member (EventLogEffect (ChainEvent t)) effs
    , Pretty t
    )
    => ContractInstanceId
    -> Eff effs ()
reportContractStatus cid = do
    logInfo "Finding Contract"
    statuses <- runGlobalQuery (Query.latestContractStatus @t)
    logInfo $ render $ pretty $ Map.lookup cid statuses

installedContracts :: forall t effs. (Ord t, Member (EventLogEffect (ChainEvent t)) effs) => Eff effs (Set t)
installedContracts = runGlobalQuery Query.installedContractsProjection

activeContracts :: forall t effs. (Ord t, Member (EventLogEffect (ChainEvent t)) effs) => Eff effs (Map.Map t (Set ContractInstanceId))
activeContracts = runGlobalQuery Query.activeContractsProjection

txHistory :: forall t effs. (Member (EventLogEffect (ChainEvent t)) effs) => Eff effs [Ledger.Tx]
txHistory = runGlobalQuery (Query.txHistoryProjection @t)

activeContractHistory ::
       Member (EventLogEffect (ChainEvent t)) effs => ContractInstanceId -> Eff effs [ContractInstanceState t]
activeContractHistory = runGlobalQuery . Query.activeContractHistoryProjection

------------------------------------------------------------
-- | Create a database 'Connection' containing the connection pool
-- plus some configuration information.
dbConnect ::
    ( MonadUnliftIO m
    , MonadLogger m
    )
    => DbConfig
    -> m EventLog.Connection
dbConnect DbConfig {dbConfigFile, dbConfigPoolSize} = do
    let connectionInfo = mkSqliteConnectionInfo dbConfigFile
    MonadLogger.logDebugN "Connecting to DB"
    connectionPool <- createSqlitePoolFromInfo connectionInfo dbConfigPoolSize
    pure $ EventLog.Connection (defaultSqlEventStoreConfig, connectionPool)

type SCBEffects =
        '[ GenRandomTx
        , NodeFollowerEffect
        , WalletEffect
        , UUIDEffect
        , ContractEffect ContractExe
        , ChainIndexEffect
        , NodeClientEffect
        , SigningProcessEffect
        , EventLogEffect (ChainEvent ContractExe)
        , Log
        ]
