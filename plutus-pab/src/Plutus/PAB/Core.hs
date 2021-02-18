{-# LANGUAGE AllowAmbiguousTypes   #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE DeriveGeneric         #-}
{-# LANGUAGE DerivingStrategies    #-}
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

module Plutus.PAB.Core
    ( dbConnect
    , installContract
    , activateContract
    , activateContractSTM
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

import           Cardano.BM.Data.Tracer           (ToObject (..), TracingVerbosity (..))
import           Cardano.BM.Data.Tracer.Extras    (StructuredLog, mkObjectStr)
import           Control.Monad                    (void)
import           Control.Monad.Freer              (Eff, Member)
import           Control.Monad.Freer.Error        (Error)
import           Control.Monad.Freer.Extras.Log   (LogMsg, logInfo)
import           Control.Monad.IO.Unlift          (MonadUnliftIO)
import           Control.Monad.Logger             (MonadLogger)
import qualified Control.Monad.Logger             as MonadLogger
import           Data.Aeson                       (FromJSON, ToJSON (..))
import qualified Data.Map.Strict                  as Map
import           Data.Set                         (Set)
import           Data.Text.Prettyprint.Doc        (Pretty, pretty, (<+>))
import           Database.Persist.Sqlite          (createSqlitePoolFromInfo, mkSqliteConnectionInfo)
import           Eventful.Store.Sql               (defaultSqlEventStoreConfig)
import           GHC.Generics                     (Generic)
import qualified Ledger
import           Plutus.PAB.Command               (installCommand)
import           Plutus.PAB.Core.ContractInstance (activateContract, activateContractSTM, callContractEndpoint,
                                                   processAllContractInboxes, processAllContractOutboxes,
                                                   processContractInbox)
import           Plutus.PAB.Effects.Contract      (ContractCommand (..), ContractEffect, invokeContract)
import           Plutus.PAB.Effects.EventLog      (Connection (..), EventLogEffect, refreshProjection, runCommand,
                                                   runGlobalQuery)
import qualified Plutus.PAB.Effects.EventLog      as EventLog
import           Plutus.PAB.Effects.UUID          (UUIDEffect)
import           Plutus.PAB.Events                (ChainEvent, ContractInstanceId, ContractInstanceState)
import qualified Plutus.PAB.Query                 as Query
import           Plutus.PAB.Types                 (DbConfig (DbConfig), PABError, Source (..), dbConfigFile,
                                                   dbConfigPoolSize, toUUID)

type ContractEffects t =
        '[ EventLogEffect (ChainEvent t)
         , UUIDEffect
         , ContractEffect FilePath
         , Error PABError
         ]

data CoreMsg t =
    Installing t
    | Installed
    | FindingContract ContractInstanceId
    | FoundContract (Maybe (ContractInstanceState t))
    deriving stock (Eq, Show, Generic)
    deriving anyclass (ToJSON, FromJSON)

instance Pretty t => Pretty (CoreMsg t) where
    pretty = \case
        Installing d      -> "Installing" <+> pretty d
        Installed         -> "Installed"
        FindingContract i -> "Finding contract" <+> pretty i
        FoundContract c   -> "Found contract" <+> pretty c

instance (StructuredLog t, ToJSON t) => ToObject (CoreMsg t) where
    toObject v = \case
        Installing t ->
            mkObjectStr "installing contract" t
        Installed ->
            mkObjectStr "contract installed" ()
        FindingContract instanceID ->
            mkObjectStr "finding contract instance" instanceID
        FoundContract state ->
            mkObjectStr "found contract" $
                case v of
                    MaximalVerbosity -> Left state
                    _                -> Right ()

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
