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
    EventfulBackend(..),
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
import qualified Eventful.Store.Memory                          as M
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
import           Plutus.PAB.Effects.EventLog                    (Connection (..), EventLogBackend, handleEventLog)
import qualified Plutus.PAB.Effects.EventLog                    as EventLog
import           Plutus.PAB.Events                              (PABEvent)
import           Plutus.PAB.Monitoring.MonadLoggerBridge        (TraceLoggerT (..))
import           Plutus.PAB.Monitoring.Monitoring               (convertLog, handleLogMsgTrace)
import           Plutus.PAB.Monitoring.PABLogMsg                (PABLogMsg (..))
import           Plutus.PAB.Timeout                             (Timeout (..))
import           Plutus.PAB.Types                               (Config (Config), DbConfig (..), PABError (..),
                                                                 chainIndexConfig, dbConfig, endpointTimeout,
                                                                 nodeServerConfig, walletServerConfig)
import           Servant.Client                                 (ClientEnv, mkClientEnv)

------------------------------------------------------------
data AppEnv =
    AppEnv
        { dbConnection    :: EventLogBackend (PABEvent ContractExe)
        , walletClientEnv :: ClientEnv
        , nodeClientEnv   :: ClientEnv
        , chainIndexEnv   :: ClientEnv
        , clientHandler   :: Client.ClientHandler
        , appConfig       :: Config
        , appTrace        :: Trace IO (PABLogMsg ContractExe)
        }

appEffectHandlers :: EventfulBackend -> Config -> Trace IO (PABLogMsg ContractExe) -> EffectHandlers ContractExe AppEnv
appEffectHandlers eventfulBackend config trace =
    EffectHandlers
        { initialiseEnvironment = do
            env <- liftIO $ mkEnv eventfulBackend trace config
            let Config{nodeServerConfig=MockServerConfig{mscSocketPath, mscSlotConfig}} = config
            instancesState <- liftIO $ STM.atomically $ Instances.emptyInstancesState
            blockchainEnv <- liftIO $ BlockchainEnv.startNodeClient mscSocketPath mscSlotConfig
            pure (instancesState, blockchainEnv, env)

        , handleLogMessages =
            interpret (handleLogMsgTrace trace)
            . reinterpret (mapLog SMultiAgent)

        , handleContractStoreEffect =
            interpret (Core.handleUserEnvReader @ContractExe @AppEnv)
            . interpret (Core.handleMappedReader @AppEnv dbConnection)
            . interpret (handleEventLog @_ @(PABEvent ContractExe) (convertLog SLoggerBridge trace))
            . reinterpretN @'[_, Reader (EventLogBackend (PABEvent ContractExe)), Reader AppEnv] handleContractStore

        , handleContractEffect =
            interpret (handleLogMsgTrace trace)
            . reinterpret (mapLog @_ @(PABLogMsg ContractExe) SContractExeLogMsg)
            . reinterpret (handleContractEffectContractExe @IO)

        , handleContractDefinitionStoreEffect =
            interpret (Core.handleUserEnvReader @ContractExe @AppEnv)
            . interpret (Core.handleMappedReader @AppEnv dbConnection)
            . interpret (handleEventLog @_ @(PABEvent ContractExe) (convertLog SLoggerBridge trace))
            . reinterpretN @'[_, Reader (EventLogBackend (PABEvent ContractExe)), Reader AppEnv] handleContractDefinitionStore

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
    EventfulBackend
    -> Trace IO (PABLogMsg ContractExe) -- ^ Top-level tracer
    -> Config -- ^ Client configuration
    -> App a -- ^ Action
    -> IO (Either PABError a)
runApp eventfulBackend trace config@Config{endpointTimeout} = Core.runPAB (Timeout endpointTimeout) (appEffectHandlers eventfulBackend config trace)

type App a = PABAction ContractExe AppEnv a

data EventfulBackend = SqliteBackend | InMemoryBackend
    deriving (Eq, Ord, Show)

mkEnv :: EventfulBackend -> Trace IO (PABLogMsg ContractExe) -> Config -> IO AppEnv
mkEnv eventfulBackend appTrace appConfig@Config { dbConfig
             , nodeServerConfig =  MockServerConfig{mscBaseUrl, mscSocketPath, mscSlotConfig}
             , walletServerConfig
             , chainIndexConfig
             } = do
    walletClientEnv <- clientEnv (Wallet.baseUrl walletServerConfig)
    nodeClientEnv <- clientEnv mscBaseUrl
    chainIndexEnv <- clientEnv (ChainIndex.ciBaseUrl chainIndexConfig)
    dbConnection <- case eventfulBackend of
        SqliteBackend   -> Left <$> dbConnect appTrace dbConfig
        InMemoryBackend -> Right <$> M.eventMapTVar
    clientHandler <- liftIO $ Client.runClientNode mscSocketPath mscSlotConfig (\_ _ -> pure ())
    pure AppEnv {..}
  where
    clientEnv baseUrl = mkClientEnv <$> liftIO mkManager <*> pure (coerce baseUrl)

    mkManager =
        newManager $
        tlsManagerSettings {managerModifyRequest = pure . setRequestIgnoreStatus}

-- | Initialize/update the database to hold events.
migrate :: Trace IO (PABLogMsg ContractExe) -> DbConfig -> IO ()
migrate trace config = do
    Connection (sqlConfig, connectionPool) <- dbConnect trace config
    flip runTraceLoggerT (convertLog SLoggerBridge trace) $ do
        liftIO
            $ flip runSqlPool connectionPool
            $ initializeSqliteEventStore sqlConfig connectionPool

------------------------------------------------------------
-- | Create a database 'Connection' containing the connection pool
-- plus some configuration information.
dbConnect :: Trace IO (PABLogMsg ContractExe) -> DbConfig -> IO EventLog.Connection
dbConnect trace DbConfig {dbConfigFile, dbConfigPoolSize} =
    flip runTraceLoggerT (convertLog SLoggerBridge trace) $ do
        let connectionInfo = mkSqliteConnectionInfo dbConfigFile
        MonadLogger.logDebugN "Connecting to DB"
        connectionPool <- createSqlitePoolFromInfo connectionInfo dbConfigPoolSize
        pure $ EventLog.Connection (defaultSqlEventStoreConfig, connectionPool)
