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

import qualified Cardano.BM.Configuration.Model     as CM
import           Cardano.BM.Trace                   (Trace)
import           Cardano.ChainIndex.Client          (handleChainIndexClient)
import qualified Cardano.ChainIndex.Types           as ChainIndex
import           Cardano.Metadata.Client            (handleMetadataClient)
import           Cardano.Metadata.Types             (MetadataEffect)
import qualified Cardano.Metadata.Types             as Metadata
import           Cardano.Node.Client                (handleNodeClientClient, handleNodeFollowerClient,
                                                     handleRandomTxClient)
import           Cardano.Node.Follower              (NodeFollowerEffect)
import           Cardano.Node.RandomTx              (GenRandomTx)
import qualified Cardano.Node.Server                as NodeServer
import qualified Cardano.SigningProcess.Client      as SigningProcessClient
import qualified Cardano.SigningProcess.Server      as SigningProcess
import qualified Cardano.Wallet.Client              as WalletClient
import qualified Cardano.Wallet.Server              as WalletServer
import           Control.Monad.Catch                (MonadCatch)
import           Control.Monad.Freer
import           Control.Monad.Freer.Error          (Error, handleError, runError, throwError)
import           Control.Monad.Freer.Extra.Log      (LogMsg, handleWriterLog, logDebug, logInfo)
import           Control.Monad.Freer.Log            (LogMessage, LogObserve)
import qualified Control.Monad.Freer.Log            as Log
import           Control.Monad.Freer.Reader         (Reader, asks, runReader)
import           Control.Monad.Freer.WebSocket      (WebSocketEffect, handleWebSocket)
import           Control.Monad.Freer.Writer         (Writer)
import           Control.Monad.IO.Class             (MonadIO, liftIO)
import           Control.Monad.IO.Unlift            (MonadUnliftIO)
import           Control.Monad.Logger               (MonadLogger)
import           Control.Tracer                     (natTracer)
import           Data.Aeson                         (FromJSON, eitherDecode)
import qualified Data.Aeson.Encode.Pretty           as JSON
import           Data.Bifunctor                     (Bifunctor (..))
import qualified Data.ByteString.Lazy.Char8         as BSL8
import           Data.Functor.Contravariant         (Contravariant (..))
import qualified Data.Text                          as Text
import           Database.Persist.Sqlite            (runSqlPool)
import           Eventful.Store.Sqlite              (initializeSqliteEventStore)
import           Network.HTTP.Client                (managerModifyRequest, newManager, setRequestIgnoreStatus)
import           Network.HTTP.Client.TLS            (tlsManagerSettings)
import           Plutus.PAB.Core                    (Connection (Connection),
                                                     ContractCommand (InitContract, UpdateContract), CoreMsg, dbConnect)
import           Plutus.PAB.Core.ContractInstance   (ContractInstanceMsg)
import           Plutus.PAB.Effects.Contract        (ContractEffect (..))
import           Plutus.PAB.Effects.ContractRuntime (ContractRuntimeMsg, handleContractRuntime)
import           Plutus.PAB.Effects.EventLog        (EventLogEffect (..), handleEventLogSql)
import           Plutus.PAB.Effects.UUID            (UUIDEffect, handleUUIDEffect)
import           Plutus.PAB.Events                  (ChainEvent)
import           Plutus.PAB.MonadLoggerBridge       (TraceLoggerT (..))
import           Plutus.PAB.Monitoring              (handleLogMsgTraceMap, handleObserveTrace)
import           Plutus.PAB.PABLogMsg               (ContractExeLogMsg (..), PABLogMsg (..))
import           Plutus.PAB.ParseStringifiedJSON    (UnStringifyJSONLog)
import           Plutus.PAB.Types                   (Config (Config), ContractExe (..), PABError (..), chainIndexConfig,
                                                     dbConfig, metadataServerConfig, nodeServerConfig,
                                                     signingProcessConfig, walletServerConfig)
import           Plutus.PAB.Webserver.Types         (WebSocketLogMsg)
import           Servant.Client                     (BaseUrl, ClientEnv, ClientError, mkClientEnv)
import           System.Exit                        (ExitCode (ExitFailure, ExitSuccess))
import           System.Process                     (readProcessWithExitCode)
import           Wallet.API                         (WalletAPIError)
import           Wallet.Effects                     (ChainIndexEffect, ContractRuntimeEffect, NodeClientEffect,
                                                     SigningProcessEffect, WalletEffect)
import qualified Wallet.Emulator.Wallet


------------------------------------------------------------
data Env =
    Env
        { dbConnection      :: Connection
        , walletClientEnv   :: ClientEnv
        , nodeClientEnv     :: ClientEnv
        , metadataClientEnv :: ClientEnv
        , signingProcessEnv :: ClientEnv
        , chainIndexEnv     :: ClientEnv
        }

type AppBackend m =
        '[ GenRandomTx
         , ContractRuntimeEffect
         , NodeFollowerEffect
         , Error ClientError
         , WalletEffect
         , Error WalletAPIError
         , Error ClientError
         , NodeClientEffect
         , Error ClientError
         , MetadataEffect
         , Error Metadata.MetadataError
         , SigningProcessEffect
         , Error ClientError
         , UUIDEffect
         , ContractEffect ContractExe
         , ChainIndexEffect
         , Error ClientError
         , EventLogEffect (ChainEvent ContractExe)
         , WebSocketEffect
         , Error PABError
         , Writer [Wallet.Emulator.Wallet.WalletEvent]
         , LogMsg Wallet.Emulator.Wallet.WalletEvent
         , LogMsg ContractExeLogMsg
         , LogMsg ContractRuntimeMsg
         , LogMsg (ContractInstanceMsg ContractExe)
         , LogMsg WebSocketLogMsg
         , LogMsg UnStringifyJSONLog
         , LogMsg (CoreMsg ContractExe)
         , LogObserve (LogMessage Text.Text)
         , Reader Connection
         , Reader Config
         , Reader Env
         , m
         ]

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
    -> Eff (AppBackend m) a -- ^ Action
    -> m (Either PABError a)
runAppBackend trace loggingConfig config action = do
    env@Env { dbConnection
            , nodeClientEnv
            , metadataClientEnv
            , walletClientEnv
            , signingProcessEnv
            , chainIndexEnv
            } <- mkEnv config
    let
        handleChainIndex :: Eff (ChainIndexEffect ': Error ClientError ': _) a -> Eff _ a
        handleChainIndex =
            flip handleError (throwError . ChainIndexError) .
            handleChainIndexClient chainIndexEnv
        handleSigningProcess ::
               Eff (SigningProcessEffect ': Error ClientError ': _) a -> Eff _ a
        handleSigningProcess =
            flip handleError (throwError . SigningProcessError) .
            SigningProcessClient.handleSigningProcessClient signingProcessEnv
        handleNodeClient ::
               Eff (NodeClientEffect ': Error ClientError ': _) a -> Eff _ a
        handleNodeClient =
            flip handleError (throwError . NodeClientError) .
            handleNodeClientClient nodeClientEnv
        handleNodeFollower ::
               Eff (NodeFollowerEffect ': Error ClientError ': _) a -> Eff _ a
        handleNodeFollower =
            flip handleError (throwError . NodeClientError) .
            handleNodeFollowerClient nodeClientEnv
        handleMetadata ::
               Eff (MetadataEffect ': Error Metadata.MetadataError ': _) a -> Eff _ a
        handleMetadata =
            flip handleError (throwError . MetadataError) .
            handleMetadataClient metadataClientEnv
        handleWallet ::
               Eff (WalletEffect ': Error WalletAPIError ': Error ClientError ': _) a
            -> Eff _ a
        handleWallet =
            flip handleError (throwError . WalletClientError) .
            flip handleError (throwError . WalletError) .
            WalletClient.handleWalletClient walletClientEnv


    runM
        . runReader env
        . runReader config
        . runReader dbConnection
        . handleObserveTrace loggingConfig trace
        . handleLogMsgTraceMap SCoreMsg trace
        . handleLogMsgTraceMap SUnstringifyJSON trace
        . handleLogMsgTraceMap SWebsocketMsg trace
        . handleLogMsgTraceMap SContractInstanceMsg trace
        . handleLogMsgTraceMap SContractRuntimeMsg trace
        . handleLogMsgTraceMap SContractExeLogMsg trace
        . handleLogMsgTraceMap SWalletEvent trace
        . handleWriterLog (\_ -> Log.Info)
        . runError
        . handleWebSocket
        . handleEventLogSql
        . handleChainIndex
        . handleContractEffectApp
        . handleUUIDEffect
        . handleSigningProcess
        . handleMetadata
        . handleNodeClient
        . handleWallet
        . handleNodeFollower
        . interpret (handleContractRuntime @ContractExe)
        $ handleRandomTxClient nodeClientEnv action

type App a = Eff (AppBackend (TraceLoggerT IO)) a

mkEnv :: forall m. (MonadUnliftIO m, MonadLogger m) => Config -> m Env
mkEnv Config { dbConfig
             , nodeServerConfig
             , metadataServerConfig
             , walletServerConfig
             , signingProcessConfig
             , chainIndexConfig
             } = do
    walletClientEnv <- clientEnv (WalletServer.baseUrl walletServerConfig)
    nodeClientEnv <- clientEnv (NodeServer.mscBaseUrl nodeServerConfig)
    metadataClientEnv <- clientEnv (Metadata.mdBaseUrl metadataServerConfig)
    signingProcessEnv <-
        clientEnv (SigningProcess.spBaseUrl signingProcessConfig)
    chainIndexEnv <- clientEnv (ChainIndex.ciBaseUrl chainIndexConfig)
    dbConnection <- dbConnect dbConfig
    pure Env {..}
  where
    clientEnv :: BaseUrl -> m ClientEnv
    clientEnv baseUrl = mkClientEnv <$> liftIO mkManager <*> pure baseUrl

    mkManager =
        newManager $
        tlsManagerSettings {managerModifyRequest = pure . setRequestIgnoreStatus}

runApp :: Trace IO PABLogMsg -> CM.Configuration -> Config -> App a -> IO (Either PABError a)
runApp theTrace logConfig config action =
    runTraceLoggerT

    -- see note [Use of iohk-monitoring in PAB]
    (runAppBackend @(TraceLoggerT IO) (monadLoggerTracer theTrace) logConfig config action)
    (contramap (second (fmap SLoggerBridge)) theTrace)

handleContractEffectApp ::
       (Member (LogMsg ContractExeLogMsg) effs, Member (Error PABError) effs, LastMember m effs, MonadIO m)
    => Eff (ContractEffect ContractExe ': effs) ~> Eff effs
handleContractEffectApp =
    interpret $ \case
        InvokeContract contractCommand -> do
            logDebug InvokeContractMsg
            case contractCommand of
                InitContract (ContractExe contractPath) -> do
                    logDebug $ InitContractMsg contractPath
                    liftProcess $ readProcessWithExitCode contractPath ["init"] ""
                UpdateContract (ContractExe contractPath) payload -> do
                    let pl = BSL8.unpack (JSON.encodePretty payload)
                    logDebug $ UpdateContractMsg contractPath payload
                    liftProcess $ readProcessWithExitCode contractPath ["update"] pl
        ExportSchema (ContractExe contractPath) -> do
            logDebug $ ExportSignatureMsg contractPath
            liftProcess $
                readProcessWithExitCode contractPath ["export-signature"] ""

liftProcess ::
       (LastMember m effs, MonadIO m, FromJSON b, Member (LogMsg ContractExeLogMsg) effs, Member (Error PABError) effs)
    => IO (ExitCode, String, String)
    -> Eff effs b
liftProcess process = do
    (exitCode, stdout, stderr) <- sendM $ liftIO process
    case exitCode of
        ExitFailure code -> do
            logDebug $ ProcessExitFailure stderr
            throwError $ ContractCommandError code (Text.pack stderr)
        ExitSuccess -> do
            logDebug $ ContractResponse stdout
            case eitherDecode (BSL8.pack stdout) of
                Right value -> pure value
                Left err    -> throwError $ ContractCommandError 0 (Text.pack err)

-- | Initialize/update the database to hold events.
migrate :: App ()
migrate = do
    logInfo Migrating
    Connection (sqlConfig, connectionPool) <- asks dbConnection
    liftIO
        $ flip runSqlPool connectionPool
        $ initializeSqliteEventStore sqlConfig connectionPool

monadLoggerTracer :: Trace IO a -> Trace (TraceLoggerT IO) a
monadLoggerTracer = natTracer (\x -> TraceLoggerT $ \_ -> x)
