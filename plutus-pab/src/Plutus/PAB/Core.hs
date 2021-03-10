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
    , activateContractSTM
    , reportContractState
    , installedContracts
    , activeContracts
    , txHistory
    , activeContractHistory
    , Connection(Connection)
    , refreshProjection
    , runCommand
    , runGlobalQuery
    , Source(..)
    , toUUID
    -- * Effects
    , ContractEffects
    , CoreMsg(..)
    ) where

import           Cardano.BM.Data.Tracer                  (ToObject (..), TracingVerbosity (..))
import           Cardano.BM.Data.Tracer.Extras           (StructuredLog, mkObjectStr)
import           Control.Monad                           (void)
import           Control.Monad.Freer                     (Eff, Member)
import           Control.Monad.Freer.Error               (Error)
import           Control.Monad.Freer.Extras.Log          (LogMsg, logInfo)
import           Control.Monad.IO.Unlift                 (MonadUnliftIO)
import           Control.Monad.Logger                    (MonadLogger)
import qualified Control.Monad.Logger                    as MonadLogger
import           Data.Aeson                              (FromJSON, ToJSON (..))
import qualified Data.Map.Strict                         as Map
import           Data.Set                                (Set)
import           Data.Text.Prettyprint.Doc               (Pretty, pretty, (<+>))
import           Database.Persist.Sqlite                 (createSqlitePoolFromInfo, mkSqliteConnectionInfo)
import           Eventful.Store.Sql                      (defaultSqlEventStoreConfig)
import           GHC.Generics                            (Generic)
import qualified Ledger
import           Plutus.PAB.Command                      (installCommand)
import           Plutus.PAB.Core.ContractInstance        (activateContractSTM)
import           Plutus.PAB.Effects.Contract             (ContractEffect)
import           Plutus.PAB.Effects.EventLog             (Connection (..), EventLogEffect, refreshProjection,
                                                          runCommand, runGlobalQuery)
import qualified Plutus.PAB.Effects.EventLog             as EventLog
import           Plutus.PAB.Effects.UUID                 (UUIDEffect)
import           Plutus.PAB.Events                       (PABEvent)
import           Plutus.PAB.Events.Contract              (ContractPABRequest)
import           Plutus.PAB.Events.ContractInstanceState (PartiallyDecodedResponse)
import qualified Plutus.PAB.Query                        as Query
import           Plutus.PAB.Types                        (DbConfig (DbConfig), PABError, Source (..), dbConfigFile,
                                                          dbConfigPoolSize, toUUID)
import           Wallet.Types                            (ContractInstanceId)

type ContractEffects t =
        '[ EventLogEffect (PABEvent t)
         , UUIDEffect
         , ContractEffect FilePath
         , Error PABError
         ]

data CoreMsg t =
    Installing t
    | Installed
    | FindingContract ContractInstanceId
    | FoundContract (Maybe (PartiallyDecodedResponse ContractPABRequest))
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
    , Member (EventLogEffect (PABEvent t)) effs
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
    , Member (EventLogEffect (PABEvent t)) effs
    )
    => ContractInstanceId
    -> Eff effs ()
reportContractState cid = do
    logInfo @(CoreMsg t) $ FindingContract cid
    contractState <- runGlobalQuery (Query.contractState @t)
    logInfo @(CoreMsg t) $ FoundContract (Map.lookup cid contractState)

installedContracts :: forall t effs. (Ord t, Member (EventLogEffect (PABEvent t)) effs) => Eff effs (Set t)
installedContracts = runGlobalQuery Query.installedContractsProjection

activeContracts :: forall t effs. (Ord t, Member (EventLogEffect (PABEvent t)) effs) => Eff effs (Map.Map t (Set ContractInstanceId))
activeContracts = runGlobalQuery Query.activeContractsProjection

txHistory :: forall t effs. (Member (EventLogEffect (PABEvent t)) effs) => Eff effs [Ledger.Tx]
txHistory = runGlobalQuery (Query.txHistoryProjection @t)

activeContractHistory ::
    forall t effs.
    Member (EventLogEffect (PABEvent t)) effs => ContractInstanceId -> Eff effs [PartiallyDecodedResponse ContractPABRequest]
activeContractHistory = runGlobalQuery . Query.activeContractHistoryProjection @t

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
