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
    , Connection(Connection)
    , toUUID
    -- * Effects
    , CoreMsg(..)
    ) where

import           Cardano.BM.Data.Tracer                  (ToObject (..), TracingVerbosity (..))
import           Cardano.BM.Data.Tracer.Extras           (StructuredLog, mkObjectStr)
import           Cardano.ChainIndex.Server               (ChainIndexServerMsg)
import           Cardano.Metadata.Types                  (MetadataLogMessage)
import           Control.Monad.Freer                     (Eff, LastMember, Member, type (~>))
import           Control.Monad.Freer.Error               (Error)
import           Control.Monad.Freer.Extras.Log          (LogMsg, logInfo)
import           Control.Monad.Freer.Reader              (Reader)
import           Control.Monad.IO.Class                  (MonadIO (..))
import           Control.Monad.IO.Unlift                 (MonadUnliftIO)
import           Control.Monad.Logger                    (MonadLogger)
import qualified Control.Monad.Logger                    as MonadLogger
import           Data.Aeson                              (FromJSON, ToJSON (..))
import           Data.Text.Prettyprint.Doc               (Pretty, pretty, (<+>))
import           Database.Persist.Sqlite                 (createSqlitePoolFromInfo, mkSqliteConnectionInfo)
import           Eventful.Store.Sql                      (defaultSqlEventStoreConfig)
import           GHC.Generics                            (Generic)
import           Plutus.PAB.Core.ContractInstance        (activateContractSTM)
import           Plutus.PAB.Core.ContractInstance.STM    (BlockchainEnv, InstancesState)
import           Plutus.PAB.Effects.Contract             (ContractDefinitionStore, ContractEffect, ContractEffectMsg,
                                                          ContractStore, PABContract (..), addDefinition, getState)
import           Plutus.PAB.Effects.EventLog             (Connection (..))
import qualified Plutus.PAB.Effects.EventLog             as EventLog
import           Plutus.PAB.Events.Contract              (ContractPABRequest)
import           Plutus.PAB.Events.ContractInstanceState (PartiallyDecodedResponse)
import           Plutus.PAB.Monitoring.PABLogMsg         ()
import           Plutus.PAB.Types                        (DbConfig (DbConfig), PABError, dbConfigFile, dbConfigPoolSize,
                                                          toUUID)
import           Wallet.Effects                          (ChainIndexEffect, NodeClientEffect, WalletEffect)
import           Wallet.Emulator.Wallet                  (Wallet)
import           Wallet.Types                            (ContractInstanceId)


-- | Effect handlers for running the PAB.
data EffectHandlers t env =
    EffectHandlers
        { -- | Create the initial environment. This value is shared between all threads
          --   started by the PAB.
          initialiseEnvironment :: forall m effs.
            ( Member (Reader BlockchainEnv) effs
            , Member (Reader InstancesState) effs
            , Member (Error PABError) effs
            , MonadIO m
            , LastMember m effs
            )
            => Eff effs env

        -- | Handle log messages
        , handleLogMessages :: forall m effs.
            ( Member (Reader BlockchainEnv) effs
            , Member (Reader InstancesState) effs
            , Member (Reader env) effs
            , Member (Error PABError) effs
            , MonadIO m
            , LastMember m effs
            )
            => Eff (LogMsg PABMultiAgentMsg ': effs)
            ~> Eff effs

        -- | Handle the 'ContractStore' effect
        , handleContractStoreEffect :: forall m effs.
            ( Member (Reader env) effs
            , Member (Error PABError) effs
            , Member (LogMsg PABMultiAgentMsg) effs
            , MonadIO m
            , LastMember m effs
            )
            => Eff (ContractStore t ': effs)
            ~> Eff effs

        -- | Handle the 'ContractEffect'
        , handleContractEffect :: forall m effs.
            ( Member (Reader env) effs
            , Member (Error PABError) effs
            , Member (LogMsg PABMultiAgentMsg) effs
            , MonadIO m
            , LastMember m effs
            )
            => Eff (ContractEffect t ': effs)
            ~> Eff effs

        -- | Handle effects that serve requests to external services managed by the PAB
        --   Runs in the context of a particular wallet (note the 'Reader Wallet' effect)
        , handleServicesEffects :: forall m effs.
            ( Member (Reader env) effs
            , Member (Error PABError) effs
            , Member (LogMsg PABMultiAgentMsg) effs
            , Member (Reader Wallet) effs
            , LastMember IO effs
            )
            => Eff (WalletEffect ': NodeClientEffect ': ChainIndexEffect ': effs)
            ~> Eff effs

        -- | Action to run on startup
        , onStartup :: forall m effs.
            ( Member (Reader env) effs
            , Member (Error PABError) effs
            , Member (LogMsg PABMultiAgentMsg) effs
            , MonadIO m
            , LastMember m effs
            ) => Eff effs ()

        -- | Action to run on shutdown
        , onShutdown :: forall m effs.
            ( Member (Reader env) effs
            , Member (Error PABError) effs
            , Member (LogMsg PABMultiAgentMsg) effs
            , MonadIO m
            , LastMember m effs
            ) => Eff effs ()
        }

-- -- | 'EffectHandlers' for running the PAB as a simulator (no connectivity to
-- --   out-of-process services such as wallet backend, node, etc.)
-- simulatorHandlers :: EffectHandlers TestContracts (SimulatorState TestContracts)
-- simulatorHandlers =
--     EffectHandlers
--         { initialiseEnvironment = liftIO Simulator.initialState
--         , handleContractStoreEffect =
--             interpret handleContractStore
--         , handleContractEffect =
--             handleContractTestMsg
--             . reinterpret handleContractTest
--         , handleLogMessages = undefined -- FIXME
--         , handleServicesEffects = undefined -- FIXME
--         , onStartup = pure () -- FIXME: Start clock thread
--         , onShutdown = pure ()
--         }

-- applicationHandlers :: EffectHandlers ContractExe ()
-- applicationHandlers = undefined

installContract ::
    forall t effs.
    ( Member (LogMsg (CoreMsg (ContractDef t))) effs
    , Member (ContractDefinitionStore t) effs
    )
    => (ContractDef t)
    -> Eff effs ()
installContract contractHandle = do
    logInfo @(CoreMsg (ContractDef t)) $ Installing contractHandle
    addDefinition @t contractHandle
    logInfo @(CoreMsg (ContractDef t)) Installed

reportContractState ::
    forall t effs.
    ( Member (LogMsg (CoreMsg t)) effs
    , Member (ContractStore t) effs
    , State t ~ PartiallyDecodedResponse ContractPABRequest
    )
    => ContractInstanceId
    -> Eff effs ()
reportContractState cid = do
    logInfo @(CoreMsg t) $ FindingContract cid
    contractState <- getState @t cid
    logInfo @(CoreMsg t) $ FoundContract $ Just contractState

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
