{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DerivingStrategies    #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns        #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE RecordWildCards       #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE StrictData            #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeOperators         #-}
{-# OPTIONS_GHC -fno-warn-partial-type-signatures #-}

module Plutus.PAB.App where

import qualified Cardano.BM.Configuration.Model                 as CM
import           Cardano.BM.Trace                               (Trace)
-- import           Cardano.ChainIndex.Client                      (handleChainIndexClient)
import qualified Cardano.ChainIndex.Types                       as ChainIndex
-- import           Cardano.Node.Client                            (handleNodeClientClient)
import qualified Cardano.Protocol.Socket.Client          as Client
import           Cardano.Node.Types                             (MockServerConfig (..))
-- import qualified Cardano.Wallet.Client                          as WalletClient
import qualified Cardano.Wallet.Types                           as Wallet
import           Control.Monad.Catch                            (MonadCatch)
import           Control.Monad.Freer
-- import           Control.Monad.Freer.Error                      (Error, handleError, runError, throwError)
import qualified Control.Concurrent.STM                         as STM
import           Control.Monad.Freer.Extras.Log                 (mapLog)
import           Control.Monad.Freer.Reader                     (Reader, asks, runReader)
import           Control.Monad.Freer.WebSocket                  (WebSocketEffect, handleWebSocket)
import           Control.Monad.IO.Class                         (MonadIO, liftIO)
import           Control.Monad.IO.Unlift                        (MonadUnliftIO)
import           Control.Monad.Logger                           (MonadLogger)
import qualified Control.Monad.Logger                           as MonadLogger
import           Data.Bifunctor                                 (Bifunctor (..))
import           Data.Coerce                                    (coerce)
import           Data.Functor.Contravariant                     (Contravariant (..))
import qualified Data.Text                                      as Text
import           Database.Persist.Sqlite                        (createSqlitePoolFromInfo, mkSqliteConnectionInfo,
                                                                 runSqlPool)
import           Eventful.Store.Sqlite                          (defaultSqlEventStoreConfig, initializeSqliteEventStore)
import           Network.HTTP.Client                            (managerModifyRequest, newManager,
                                                                 setRequestIgnoreStatus)
import           Network.HTTP.Client.TLS                        (tlsManagerSettings)
import           Plutus.PAB.Core                                (EffectHandlers (..), PABAction)
import qualified Plutus.PAB.Core.ContractInstance.BlockchainEnv as BlockchainEnv
import           Plutus.PAB.Core.ContractInstance.STM           (InstancesState)
import           Plutus.PAB.Core.ContractInstance.STM           as Instances
import           Plutus.PAB.Db.Eventful.ContractDefinitionStore (handleContractDefinitionStore)
import           Plutus.PAB.Db.Eventful.ContractStore           (handleContractStore)
import           Plutus.PAB.Effects.Contract                    (ContractDefinitionStore, ContractEffect (..),
                                                                 ContractStore)
import           Plutus.PAB.Effects.Contract.ContractExe                (ContractExe, ContractExeLogMsg (..),
                                                                 handleContractEffectContractExe)
import           Plutus.PAB.Effects.ContractRuntime             (handleContractRuntime)
import           Plutus.PAB.Effects.EventLog                    (Connection (..), EventLogEffect (..),
                                                                 handleEventLogSql)
import qualified Plutus.PAB.Effects.EventLog                    as EventLog
import           Plutus.PAB.Effects.UUID                        (UUIDEffect, handleUUIDEffect)
import           Plutus.PAB.Events                              (PABEvent)
import           Plutus.PAB.Monitoring.MonadLoggerBridge        (TraceLoggerT (..), monadLoggerTracer)
import           Plutus.PAB.Monitoring.Monitoring               (handleLogMsgTrace, handleObserveTrace)
import           Plutus.PAB.Monitoring.PABLogMsg                (PABLogMsg (..), PABMultiAgentMsg (..))
import           Plutus.PAB.Types                               (Config (Config), DbConfig (..), PABError (..),
                                                                 chainIndexConfig, dbConfig, nodeServerConfig,
                                                                 walletServerConfig)
import           Servant.Client                                 (ClientEnv, ClientError, mkClientEnv)
import           Wallet.Effects                                 (ChainIndexEffect, ContractRuntimeEffect,
                                                                 NodeClientEffect, WalletEffect)

------------------------------------------------------------
data AppEnv =
    AppEnv
        { dbConnection    :: Connection
        , walletClientEnv :: ClientEnv
        , nodeClientEnv   :: ClientEnv
        , chainIndexEnv   :: ClientEnv
        , clientHandler     :: Client.ClientHandler
        }

appEffectHandlers :: Config -> Trace IO PABLogMsg -> EffectHandlers ContractExe AppEnv
appEffectHandlers config trace =
    EffectHandlers
        { initialiseEnvironment = do
            env <- liftIO $ mkEnv trace config
            let Config{nodeServerConfig=MockServerConfig{mscSocketPath}} = config
            instancesState <- liftIO $ STM.atomically $ Instances.emptyInstancesState
            blockchainEnv <- liftIO $ BlockchainEnv.startNodeClient mscSocketPath instancesState
            pure (instancesState, blockchainEnv, env)

        , handleLogMessages =
            handleLogMsgTrace trace
            . reinterpret (mapLog SMultiAgent)

        , handleContractStoreEffect = undefined
            -- handleEventLogSql
            -- . reinterpret handleContractStore

        , handleContractEffect = undefined
            -- interpret handleContractEffectContractExe

        , handleContractDefinitionStoreEffect = undefined
            -- interpret handleContractDefinitionStore

        , handleServicesEffects = undefined

        , onStartup = pure ()

        , onShutdown = pure ()
        }

runAppBackend ::
    forall m a.
    ( MonadIO m
    , MonadUnliftIO m
    , MonadLogger m
    , MonadCatch m
    )
    => Trace m PABLogMsg -- ^ Top-level tracer
    -> CM.Configuration -- ^ Logging / monitoring configuration
    -> Config -- ^ Client configuration
    -> App a -- ^ Action
    -> IO (Either PABError a)
runAppBackend trace loggingConfig config action = do
    undefined
        -- wllt = Wallet.wallet $ walletServerConfig config
        -- handleChainIndex :: Eff (ChainIndexEffect ': _) a -> Eff _ a
        -- handleChainIndex =
        --     flip handleError (throwError . ChainIndexError) .
        --     reinterpret @_ @(Error ClientError) (handleChainIndexClient chainIndexEnv)
        -- handleNodeClient ::
        --        Eff (NodeClientEffect ': _) a -> Eff _ a
        -- handleNodeClient =
        --     flip handleError (throwError . NodeClientError) .
        --     reinterpret @_ @(Error ClientError) (handleNodeClientClient nodeClientEnv)
        -- handleWallet ::
        --        Eff (WalletEffect ': _) a
        --     -> Eff _ a
        -- handleWallet =
        --     flip handleError (throwError . WalletClientError) .
        --     flip handleError (throwError . WalletError) .
        --     reinterpret2 (WalletClient.handleWalletClient walletClientEnv wllt)

type App a = PABAction ContractExe AppEnv a

mkEnv :: Trace IO PABLogMsg -> Config -> IO AppEnv
mkEnv trace Config { dbConfig
             , nodeServerConfig
             , walletServerConfig
             , chainIndexConfig
             } = do
    walletClientEnv <- clientEnv (Wallet.baseUrl walletServerConfig)
    nodeClientEnv <- clientEnv (mscBaseUrl nodeServerConfig)
    chainIndexEnv <- clientEnv (ChainIndex.ciBaseUrl chainIndexConfig)
    dbConnection <-  runTraceLoggerT
                        (dbConnect dbConfig)
                        (contramap (second (fmap SLoggerBridge)) trace)
    clientHandler <- liftIO $ Client.runClientNode (mscSocketPath nodeServerConfig) (\_ _ -> pure ())
    pure AppEnv {..}
  where
    clientEnv baseUrl = mkClientEnv <$> liftIO mkManager <*> pure (coerce baseUrl)

    mkManager =
        newManager $
        tlsManagerSettings {managerModifyRequest = pure . setRequestIgnoreStatus}

runApp :: InstancesState -> Trace IO PABLogMsg -> CM.Configuration -> Config -> App a -> IO (Either PABError a)
runApp instancesState theTrace logConfig config action = undefined
    -- runTraceLoggerT
    -- -- see note [Use of iohk-monitoring in PAB]
    -- (runAppBackend @(TraceLoggerT IO) instancesState (monadLoggerTracer theTrace) logConfig config action)
    -- (contramap (second (fmap SLoggerBridge)) theTrace)

-- | Initialize/update the database to hold events.
migrate :: App ()
migrate = undefined
-- migrate = interpret (mapLog SContractExeLogMsg) $ do
--     logInfo Migrating
--     Connection (sqlConfig, connectionPool) <- asks dbConnection
--     liftIO
--         $ flip runSqlPool connectionPool
--         $ initializeSqliteEventStore sqlConfig connectionPool

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
