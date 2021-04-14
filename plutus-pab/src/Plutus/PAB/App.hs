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

module Plutus.PAB.App(
    App,
    runApp,
    AppEnv(..),
    -- * App actions
    migrate,
    dbConnect
    ) where

import           Cardano.BM.Trace                               (Trace)
import           Cardano.ChainIndex.Client                      (handleChainIndexClient)
import qualified Cardano.ChainIndex.Types                       as ChainIndex
import           Cardano.Node.Client                            (handleNodeClientClient)
import           Cardano.Node.Types                             (MockServerConfig (..))
import qualified Cardano.Protocol.Socket.Client                 as Client
import qualified Cardano.Wallet.Client                          as WalletClient
import qualified Cardano.Wallet.Types                           as Wallet
import qualified Control.Concurrent.STM                         as STM
import           Control.Monad.Freer
import           Control.Monad.Freer.Error                      (handleError, throwError)
import           Control.Monad.Freer.Extras.Log                 (mapLog)
import           Control.Monad.Freer.Reader                     (Reader)
import           Control.Monad.IO.Class                         (MonadIO (..))
import qualified Control.Monad.Logger                           as MonadLogger
import           Data.Coerce                                    (coerce)
import           Database.Persist.Sqlite                        (createSqlitePoolFromInfo, mkSqliteConnectionInfo,
                                                                 runSqlPool)
import           Eventful.Store.Sqlite                          (defaultSqlEventStoreConfig, initializeSqliteEventStore)
import           Network.HTTP.Client                            (managerModifyRequest, newManager,
                                                                 setRequestIgnoreStatus)
import           Network.HTTP.Client.TLS                        (tlsManagerSettings)
import           Plutus.PAB.Core                                (EffectHandlers (..), PABAction)
import qualified Plutus.PAB.Core                                as Core
import qualified Plutus.PAB.Core.ContractInstance.BlockchainEnv as BlockchainEnv
import           Plutus.PAB.Core.ContractInstance.STM           as Instances
import           Plutus.PAB.Db.Eventful.ContractDefinitionStore (handleContractDefinitionStore)
import           Plutus.PAB.Db.Eventful.ContractStore           (handleContractStore)
import           Plutus.PAB.Effects.Contract.ContractExe        (ContractExe, handleContractEffectContractExe)
import           Plutus.PAB.Effects.EventLog                    (Connection (..), handleEventLogSql)
import qualified Plutus.PAB.Effects.EventLog                    as EventLog
import           Plutus.PAB.Events                              (PABEvent)
import           Plutus.PAB.Monitoring.MonadLoggerBridge        (TraceLoggerT (..))
import           Plutus.PAB.Monitoring.Monitoring               (convertLog, handleLogMsgTrace)
import           Plutus.PAB.Monitoring.PABLogMsg                (PABLogMsg (..))
import           Plutus.PAB.Types                               (Config (Config), DbConfig (..), PABError (..),
                                                                 chainIndexConfig, dbConfig, nodeServerConfig,
                                                                 walletServerConfig)
import           Servant.Client                                 (ClientEnv, mkClientEnv)

------------------------------------------------------------
data AppEnv =
    AppEnv
        { dbConnection    :: Connection
        , walletClientEnv :: ClientEnv
        , nodeClientEnv   :: ClientEnv
        , chainIndexEnv   :: ClientEnv
        , clientHandler   :: Client.ClientHandler
        , appConfig       :: Config
        , appTrace        :: Trace IO PABLogMsg
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
            interpret (handleLogMsgTrace trace)
            . reinterpret (mapLog SMultiAgent)

        , handleContractStoreEffect =
            interpret (Core.handleUserEnvReader @ContractExe @AppEnv)
            . interpret (Core.handleMappedReader @AppEnv @Connection dbConnection)
            . interpret (handleEventLogSql @_ @(PABEvent ContractExe) (convertLog SLoggerBridge trace))
            . reinterpretN @'[_, Reader Connection, Reader AppEnv] handleContractStore

        , handleContractEffect =
            interpret (handleLogMsgTrace trace)
            . reinterpret (mapLog SContractExeLogMsg)
            . reinterpret (handleContractEffectContractExe @IO)

        , handleContractDefinitionStoreEffect =
            interpret (Core.handleUserEnvReader @ContractExe @AppEnv)
            . interpret (Core.handleMappedReader @AppEnv @Connection dbConnection)
            . interpret (handleEventLogSql @_ @(PABEvent ContractExe) (convertLog SLoggerBridge trace))
            . reinterpretN @'[_, Reader Connection, Reader AppEnv] handleContractDefinitionStore

        , handleServicesEffects = \wallet ->

            -- handle 'NodeClientEffect'
            flip handleError (throwError . NodeClientError)
            . interpret (Core.handleUserEnvReader @ContractExe @AppEnv)
            . reinterpret (Core.handleMappedReader @AppEnv @Client.ClientHandler clientHandler)
            . interpret (Core.handleUserEnvReader @ContractExe @AppEnv)
            . reinterpret (Core.handleMappedReader @AppEnv @ClientEnv nodeClientEnv)
            . reinterpretN @'[_, _, _] (handleNodeClientClient @IO)

            -- handle 'ChainIndexEffect'
            . flip handleError (throwError . ChainIndexError)
            . interpret (Core.handleUserEnvReader @ContractExe @AppEnv)
            . reinterpret (Core.handleMappedReader @AppEnv @ClientEnv chainIndexEnv)
            . reinterpret2 (handleChainIndexClient @IO)

            -- handle 'WalletEffect'
            . flip handleError (throwError . WalletClientError)
            . flip handleError (throwError . WalletError)
            . interpret (Core.handleUserEnvReader @ContractExe @AppEnv)
            . reinterpret (Core.handleMappedReader @AppEnv @ClientEnv walletClientEnv)
            . reinterpretN @'[_, _, _] (WalletClient.handleWalletClient @IO wallet)

        , onStartup = pure ()

        , onShutdown = pure ()
        }

runApp ::
    forall a.
    Trace IO PABLogMsg -- ^ Top-level tracer
    -> Config -- ^ Client configuration
    -> App a -- ^ Action
    -> IO (Either PABError a)
runApp trace config = Core.runPAB (appEffectHandlers config trace)

type App a = PABAction ContractExe AppEnv a

mkEnv :: Trace IO PABLogMsg -> Config -> IO AppEnv
mkEnv appTrace appConfig@Config { dbConfig
             , nodeServerConfig
             , walletServerConfig
             , chainIndexConfig
             } = do
    walletClientEnv <- clientEnv (Wallet.baseUrl walletServerConfig)
    nodeClientEnv <- clientEnv (mscBaseUrl nodeServerConfig)
    chainIndexEnv <- clientEnv (ChainIndex.ciBaseUrl chainIndexConfig)
    dbConnection <-  dbConnect appTrace dbConfig
    clientHandler <- liftIO $ Client.runClientNode (mscSocketPath nodeServerConfig) (\_ _ -> pure ())
    pure AppEnv {..}
  where
    clientEnv baseUrl = mkClientEnv <$> liftIO mkManager <*> pure (coerce baseUrl)

    mkManager =
        newManager $
        tlsManagerSettings {managerModifyRequest = pure . setRequestIgnoreStatus}

-- | Initialize/update the database to hold events.
migrate :: Trace IO PABLogMsg -> DbConfig -> IO ()
migrate trace config = do
    Connection (sqlConfig, connectionPool) <- dbConnect trace config
    flip runTraceLoggerT (convertLog SLoggerBridge trace) $ do
        liftIO
            $ flip runSqlPool connectionPool
            $ initializeSqliteEventStore sqlConfig connectionPool

------------------------------------------------------------
-- | Create a database 'Connection' containing the connection pool
-- plus some configuration information.
dbConnect :: Trace IO PABLogMsg -> DbConfig -> IO EventLog.Connection
dbConnect trace DbConfig {dbConfigFile, dbConfigPoolSize} =
    flip runTraceLoggerT (convertLog SLoggerBridge trace) $ do
        let connectionInfo = mkSqliteConnectionInfo dbConfigFile
        MonadLogger.logDebugN "Connecting to DB"
        connectionPool <- createSqlitePoolFromInfo connectionInfo dbConfigPoolSize
        pure $ EventLog.Connection (defaultSqlEventStoreConfig, connectionPool)
