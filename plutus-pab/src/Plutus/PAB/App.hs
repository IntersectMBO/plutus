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
{-# LANGUAGE RecordWildCards       #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE StrictData            #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeOperators         #-}
{-# OPTIONS_GHC -fno-warn-partial-type-signatures #-}

module Plutus.PAB.App where

import qualified Cardano.BM.Configuration.Model                 as CM
import           Cardano.BM.Trace                               (Trace)
import           Cardano.ChainIndex.Client                      (handleChainIndexClient)
import qualified Cardano.ChainIndex.Types                       as ChainIndex
import           Cardano.Metadata.Client                        (handleMetadataClient)
import           Cardano.Metadata.Types                         (MetadataEffect)
import qualified Cardano.Metadata.Types                         as Metadata
import           Cardano.Node.Client                            (handleNodeClientClient, handleRandomTxClient)
import           Cardano.Node.RandomTx                          (GenRandomTx)
import           Cardano.Node.Types                             (MockServerConfig (..))
import qualified Cardano.Wallet.Client                          as WalletClient
import qualified Cardano.Wallet.Types                           as Wallet
import           Control.Monad.Catch                            (MonadCatch)
import           Control.Monad.Freer
import           Control.Monad.Freer.Error                      (Error, handleError, runError, throwError)
import           Control.Monad.Freer.Extras.Log                 (LogMessage, LogMsg, LogObserve, logInfo, mapLog)
import           Control.Monad.Freer.Reader                     (Reader, asks, runReader)
import           Control.Monad.Freer.WebSocket                  (WebSocketEffect, handleWebSocket)
import           Control.Monad.IO.Class                         (MonadIO, liftIO)
import           Control.Monad.IO.Unlift                        (MonadUnliftIO)
import           Control.Monad.Logger                           (MonadLogger)
import           Data.Bifunctor                                 (Bifunctor (..))
import           Data.Coerce                                    (coerce)
import           Data.Functor.Contravariant                     (Contravariant (..))
import qualified Data.Text                                      as Text
import           Database.Persist.Sqlite                        (runSqlPool)
import           Eventful.Store.Sqlite                          (initializeSqliteEventStore)
import           Network.HTTP.Client                            (managerModifyRequest, newManager,
                                                                 setRequestIgnoreStatus)
import           Network.HTTP.Client.TLS                        (tlsManagerSettings)
import           Plutus.PAB.Core                                (Connection (Connection), dbConnect)
import           Plutus.PAB.Core.ContractInstance.STM           (InstancesState)
import           Plutus.PAB.Db.Eventful.ContractDefinitionStore (handleContractDefinitionStore)
import           Plutus.PAB.Db.Eventful.ContractStore           (handleContractStore)
import           Plutus.PAB.Effects.Contract                    (ContractDefinitionStore, ContractEffect (..),
                                                                 ContractStore)
import           Plutus.PAB.Effects.Contract.CLI                (ContractExe, ContractExeLogMsg (..),
                                                                 handleContractEffectContractExe)
import           Plutus.PAB.Effects.ContractRuntime             (handleContractRuntime)
import           Plutus.PAB.Effects.EventLog                    (EventLogEffect (..), handleEventLogSql)
import           Plutus.PAB.Effects.UUID                        (UUIDEffect, handleUUIDEffect)
import           Plutus.PAB.Events                              (PABEvent)
import           Plutus.PAB.Monitoring.MonadLoggerBridge        (TraceLoggerT (..), monadLoggerTracer)
import           Plutus.PAB.Monitoring.Monitoring               (handleLogMsgTrace, handleObserveTrace)
import           Plutus.PAB.Monitoring.PABLogMsg                (PABLogMsg (..))
import           Plutus.PAB.Types                               (Config (Config), PABError (..), chainIndexConfig,
                                                                 dbConfig, metadataServerConfig, nodeServerConfig,
                                                                 walletServerConfig)
import           Servant.Client                                 (ClientEnv, ClientError, mkClientEnv)
import           Wallet.Effects                                 (ChainIndexEffect, ContractRuntimeEffect,
                                                                 NodeClientEffect, WalletEffect)

------------------------------------------------------------
data Env =
    Env
        { dbConnection      :: Connection
        , walletClientEnv   :: ClientEnv
        , nodeClientEnv     :: ClientEnv
        , metadataClientEnv :: ClientEnv
        , chainIndexEnv     :: ClientEnv
        , clientHandler     :: Client.ClientHandler
        }

type AppBackend m =
        '[ GenRandomTx
         , ContractRuntimeEffect
         , WalletEffect
         , NodeClientEffect
         , MetadataEffect
         , UUIDEffect
         , ContractEffect ContractExe
         , ContractDefinitionStore ContractExe
         , ContractStore ContractExe
         , ChainIndexEffect
         , EventLogEffect (PABEvent ContractExe)
         , WebSocketEffect
         , Error PABError
         , LogMsg PABLogMsg
         , LogObserve (LogMessage Text.Text)
         , Reader Connection
         , Reader Config
         , Reader Env
         , Reader InstancesState
         , m
         ]

runAppBackend ::
    forall m a.
    ( MonadIO m
    , MonadUnliftIO m
    , MonadLogger m
    , MonadCatch m
    )
    => InstancesState -- ^ State of currently active contract instances
    -> Trace m PABLogMsg -- ^ Top-level tracer
    -> CM.Configuration -- ^ Logging / monitoring configuration
    -> Config -- ^ Client configuration
    -> Eff (AppBackend m) a -- ^ Action
    -> m (Either PABError a)
runAppBackend instancesState trace loggingConfig config action = do
    env@Env { dbConnection
            , nodeClientEnv
            , metadataClientEnv
            , walletClientEnv
            , chainIndexEnv
            , clientHandler
            } <- mkEnv config
    let
        wllt = Wallet.wallet $ walletServerConfig config
        handleChainIndex :: Eff (ChainIndexEffect ': _) a -> Eff _ a
        handleChainIndex =
            flip handleError (throwError . ChainIndexError) .
            reinterpret @_ @(Error ClientError) (handleChainIndexClient chainIndexEnv)
        handleNodeClient ::
               Eff (NodeClientEffect ': _) a -> Eff _ a
        handleNodeClient =
            flip handleError (throwError . NodeClientError) .
            reinterpret @_ @(Error ClientError) (handleNodeClientClient clientHandler)
        handleMetadata ::
               Eff (MetadataEffect ': _) a -> Eff _ a
        handleMetadata =
            flip handleError (throwError . MetadataError) .
            reinterpret @_ @(Error Metadata.MetadataError) (handleMetadataClient metadataClientEnv)
        handleWallet ::
               Eff (WalletEffect ': _) a
            -> Eff _ a
        handleWallet =
            flip handleError (throwError . WalletClientError) .
            flip handleError (throwError . WalletError) .
            reinterpret2 (WalletClient.handleWalletClient walletClientEnv wllt)
        handleRandomTx :: Eff (GenRandomTx ': _) a -> Eff _ a
        handleRandomTx =
            flip handleError (throwError . RandomTxClientError) .
            reinterpret (handleRandomTxClient nodeClientEnv)


    runM
        . runReader instancesState
        . runReader env
        . runReader config
        . runReader dbConnection
        . handleObserveTrace loggingConfig trace
        . handleLogMsgTrace trace
        . runError
        . handleWebSocket
        . handleEventLogSql
        . handleChainIndex
        . interpret handleContractStore
        . interpret handleContractDefinitionStore
        . interpret (mapLog SContractExeLogMsg) . reinterpret handleContractEffectContractExe
        . handleUUIDEffect
        . handleMetadata
        . handleNodeClient
        . handleWallet
        . interpret (mapLog SContractRuntimeMsg) . interpret (mapLog SContractInstanceMsg) . reinterpret2 (handleContractRuntime @ContractExe @m)
        $ handleRandomTx action

type App a = Eff (AppBackend (TraceLoggerT IO)) a

mkEnv :: forall m. (MonadUnliftIO m, MonadLogger m) => Config -> m Env
mkEnv Config { dbConfig
             , nodeServerConfig
             , metadataServerConfig
             , walletServerConfig
             , chainIndexConfig
             } = do
    walletClientEnv <- clientEnv (Wallet.baseUrl walletServerConfig)
    nodeClientEnv <- clientEnv (mscBaseUrl nodeServerConfig)
    metadataClientEnv <- clientEnv (Metadata.mdBaseUrl metadataServerConfig)
    chainIndexEnv <- clientEnv (ChainIndex.ciBaseUrl chainIndexConfig)
    dbConnection <- dbConnect dbConfig
    clientHandler <- liftIO $ Client.runClientNode (mscSocketPath nodeServerConfig) (\_ _ -> pure ())
    pure Env {..}
  where
    clientEnv baseUrl = mkClientEnv <$> liftIO mkManager <*> pure (coerce baseUrl)

    mkManager =
        newManager $
        tlsManagerSettings {managerModifyRequest = pure . setRequestIgnoreStatus}

runApp :: InstancesState -> Trace IO PABLogMsg -> CM.Configuration -> Config -> App a -> IO (Either PABError a)
runApp instancesState theTrace logConfig config action =
    runTraceLoggerT
    -- see note [Use of iohk-monitoring in PAB]
    (runAppBackend @(TraceLoggerT IO) instancesState (monadLoggerTracer theTrace) logConfig config action)
    (contramap (second (fmap SLoggerBridge)) theTrace)

-- | Initialize/update the database to hold events.
migrate :: App ()
migrate = interpret (mapLog SContractExeLogMsg) $ do
    logInfo Migrating
    Connection (sqlConfig, connectionPool) <- asks dbConnection
    liftIO
        $ flip runSqlPool connectionPool
        $ initializeSqliteEventStore sqlConfig connectionPool
