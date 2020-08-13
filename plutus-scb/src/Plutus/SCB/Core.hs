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
    , reportContractState
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
    , Source(..)
    , toUUID
    -- * Effects
    , ContractEffects
    , CoreMsg(..)
    -- * Contract messages
    , processAllContractInboxes
    , processContractInbox
    , processAllContractOutboxes
    , callContractEndpoint
    ) where

import           Control.Monad                    (void)
import           Control.Monad.Freer              (Eff, Member)
import           Control.Monad.Freer.Error        (Error)
import           Control.Monad.Freer.Extra.Log    (LogMsg, logInfo)
import           Control.Monad.IO.Unlift          (MonadUnliftIO)
import           Control.Monad.Logger             (MonadLogger)
import qualified Control.Monad.Logger             as MonadLogger
import qualified Data.Map.Strict                  as Map
import           Data.Set                         (Set)
import           Data.Text.Prettyprint.Doc        (Pretty, pretty, (<+>))
import           Database.Persist.Sqlite          (createSqlitePoolFromInfo, mkSqliteConnectionInfo)
import           Eventful.Store.Sql               (defaultSqlEventStoreConfig)
import qualified Ledger
import           Plutus.SCB.Command               (installCommand)
import           Plutus.SCB.Core.ContractInstance (activateContract, callContractEndpoint, processAllContractInboxes,
                                                   processAllContractOutboxes, processContractInbox)
import           Plutus.SCB.Effects.Contract      (ContractCommand (..), ContractEffect, invokeContract)
import           Plutus.SCB.Effects.EventLog      (Connection (..), EventLogEffect, refreshProjection, runCommand,
                                                   runGlobalQuery)
import qualified Plutus.SCB.Effects.EventLog      as EventLog
import           Plutus.SCB.Effects.UUID          (UUIDEffect)
import           Plutus.SCB.Events                (ChainEvent, ContractInstanceId, ContractInstanceState)
import qualified Plutus.SCB.Query                 as Query
import           Plutus.SCB.Types                 (DbConfig (DbConfig), SCBError, Source (..), dbConfigFile,
                                                   dbConfigPoolSize, toUUID)

type ContractEffects t =
        '[ EventLogEffect (ChainEvent t)
         , UUIDEffect
         , ContractEffect FilePath
         , Error SCBError
         ]

data CoreMsg t =
    Installing t
    | Installed
    | FindingContract ContractInstanceId
    | FoundContract (Maybe (ContractInstanceState t))

instance Pretty t => Pretty (CoreMsg t) where
    pretty = \case
        Installing d -> "Installing" <+> pretty d
        Installed -> "Installed"
        FindingContract i -> "Finding contract" <+> pretty i
        FoundContract c -> "Found contract" <+> pretty c

installContract ::
    forall t effs.
    ( Member (LogMsg (CoreMsg t)) effs
    , Member (EventLogEffect (ChainEvent t)) effs
    )
    => t
    -> Eff effs ()
installContract contractHandle = do
    logInfo $ Installing contractHandle
    void $
        runCommand
            installCommand
            UserEventSource
            contractHandle
    logInfo @(CoreMsg t) Installed

reportContractState ::
    forall t effs.
    ( Member (LogMsg (CoreMsg t)) effs
    , Member (EventLogEffect (ChainEvent t)) effs
    )
    => ContractInstanceId
    -> Eff effs ()
reportContractState cid = do
    logInfo @(CoreMsg t) $ FindingContract cid
    contractState <- runGlobalQuery (Query.contractState @t)
    logInfo $ FoundContract (Map.lookup cid contractState)

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
