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
import           Cardano.Node.RandomTx              (GenRandomTx)
import           Cardano.Node.Types                 (MockServerConfig (..), NodeFollowerEffect)
import qualified Cardano.SigningProcess.Client      as SigningProcessClient
import qualified Cardano.SigningProcess.Types       as SigningProcess
import qualified Cardano.Wallet.Client              as WalletClient
import qualified Cardano.Wallet.Types               as Wallet
import           Control.Monad.Catch                (MonadCatch)
import           Control.Monad.Freer
import           Control.Monad.Freer.Error          (Error, handleError, runError, throwError)
import           Control.Monad.Freer.Extras.Log     (LogMessage, LogMsg, LogObserve, logDebug, logInfo, mapLog)
import           Control.Monad.Freer.Reader         (Reader, asks, runReader)
import           Control.Monad.Freer.WebSocket      (WebSocketEffect, handleWebSocket)
import           Control.Monad.IO.Class             (MonadIO, liftIO)
import           Control.Monad.IO.Unlift            (MonadUnliftIO)
import           Control.Monad.Logger               (MonadLogger)
import           Control.Tracer                     (natTracer)
import           Data.Aeson                         (FromJSON, eitherDecode)
import qualified Data.Aeson.Encode.Pretty           as JSON
import           Data.Bifunctor                     (Bifunctor (..))
import qualified Data.ByteString.Lazy.Char8         as BSL8
import           Data.Coerce                        (coerce)
import           Data.Functor.Contravariant         (Contravariant (..))
import qualified Data.Text                          as Text
import           Database.Persist.Sqlite            (runSqlPool)
import           Eventful.Store.Sqlite              (initializeSqliteEventStore)
import           Network.HTTP.Client                (managerModifyRequest, newManager, setRequestIgnoreStatus)
import           Network.HTTP.Client.TLS            (tlsManagerSettings)
import           Plutus.PAB.Core                    (Connection (Connection),
                                                     ContractCommand (InitContract, UpdateContract), dbConnect)
import           Plutus.PAB.Effects.Contract        (ContractEffect (..))
import           Plutus.PAB.Effects.ContractRuntime (handleContractRuntime)
import           Plutus.PAB.Effects.EventLog        (EventLogEffect (..), handleEventLogSql)
import           Plutus.PAB.Effects.UUID            (UUIDEffect, handleUUIDEffect)
import           Plutus.PAB.Events                  (ChainEvent)
import           Plutus.PAB.MonadLoggerBridge       (TraceLoggerT (..))
import           Plutus.PAB.Monitoring              (handleLogMsgTrace, handleObserveTrace)
import           Plutus.PAB.PABLogMsg               (ContractExeLogMsg (..), PABLogMsg (..))
import           Plutus.PAB.Types                   (Config (Config), ContractExe (..), PABError (..), chainIndexConfig,
                                                     dbConfig, metadataServerConfig, nodeServerConfig,
                                                     signingProcessConfig, walletServerConfig)
import           Servant.Client                     (BaseUrl, ClientEnv, ClientError, mkClientEnv)
import           System.Exit                        (ExitCode (ExitFailure, ExitSuccess))
import           System.Process                     (readProcessWithExitCode)
import           Wallet.Effects                     (ChainIndexEffect, ContractRuntimeEffect, NodeClientEffect,
                                                     SigningProcessEffect, WalletEffect)


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
         , WalletEffect
         , NodeClientEffect
         , MetadataEffect
         , SigningProcessEffect
         , UUIDEffect
         , ContractEffect ContractExe
         , ChainIndexEffect
         , EventLogEffect (ChainEvent ContractExe)
         , WebSocketEffect
         , Error PABError
         , LogMsg PABLogMsg
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
        handleChainIndex :: Eff (ChainIndexEffect ': _) a -> Eff _ a
        handleChainIndex =
            flip handleError (throwError . ChainIndexError) .
            reinterpret @_ @(Error ClientError) (handleChainIndexClient chainIndexEnv)
        handleSigningProcess ::
               Eff (SigningProcessEffect ': _) a -> Eff _ a
        handleSigningProcess =
            interpret (mapLog SWebsocketMsg) .
            flip handleError (throwError . SigningProcessError) .
            reinterpret2 @_ @(Error ClientError) (SigningProcessClient.handleSigningProcessClient signingProcessEnv)
        handleNodeClient ::
               Eff (NodeClientEffect ': _) a -> Eff _ a
        handleNodeClient =
            flip handleError (throwError . NodeClientError) .
            reinterpret @_ @(Error ClientError) (handleNodeClientClient nodeClientEnv)
        handleNodeFollower ::
               Eff (NodeFollowerEffect ': _) a -> Eff _ a
        handleNodeFollower =
            flip handleError (throwError . NodeClientError) .
            reinterpret @_ @(Error ClientError) (handleNodeFollowerClient nodeClientEnv)
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
            reinterpret2 (WalletClient.handleWalletClient walletClientEnv)
        handleRandomTx :: Eff (GenRandomTx ': _) a -> Eff _ a
        handleRandomTx =
            flip handleError (throwError . RandomTxClientError) .
            reinterpret (handleRandomTxClient nodeClientEnv)


    runM
        . runReader env
        . runReader config
        . runReader dbConnection
        . handleObserveTrace loggingConfig trace
        . handleLogMsgTrace trace
        . runError
        . handleWebSocket
        . handleEventLogSql
        . handleChainIndex
        . interpret (mapLog SContractExeLogMsg) . reinterpret handleContractEffectApp
        . handleUUIDEffect
        . handleSigningProcess
        . handleMetadata
        . handleNodeClient
        . handleWallet
        . handleNodeFollower
        . interpret (mapLog SContractRuntimeMsg) . interpret (mapLog SContractInstanceMsg) . reinterpret2 (handleContractRuntime @ContractExe)
        $ handleRandomTx action

type App a = Eff (AppBackend (TraceLoggerT IO)) a

mkEnv :: forall m. (MonadUnliftIO m, MonadLogger m) => Config -> m Env
mkEnv Config { dbConfig
             , nodeServerConfig
             , metadataServerConfig
             , walletServerConfig
             , signingProcessConfig
             , chainIndexConfig
             } = do
    walletClientEnv <- clientEnv (Wallet.baseUrl walletServerConfig)
    nodeClientEnv <- clientEnv (mscBaseUrl nodeServerConfig)
    metadataClientEnv <- clientEnv (Metadata.mdBaseUrl metadataServerConfig)
    signingProcessEnv <-
        clientEnv $ SigningProcess.spBaseUrl signingProcessConfig
    chainIndexEnv <- clientEnv (ChainIndex.ciBaseUrl chainIndexConfig)
    dbConnection <- dbConnect dbConfig
    pure Env {..}
  where
    clientEnv baseUrl = mkClientEnv <$> liftIO mkManager <*> pure (coerce baseUrl)

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
       ( Member (LogMsg ContractExeLogMsg) effs
       , Member (Error PABError) effs
       , LastMember m effs
       , MonadIO m)
    => ContractEffect ContractExe
    ~> Eff effs
handleContractEffectApp =
    \case
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
migrate = interpret (mapLog SContractExeLogMsg) $ do
    logInfo Migrating
    Connection (sqlConfig, connectionPool) <- asks dbConnection
    liftIO
        $ flip runSqlPool connectionPool
        $ initializeSqliteEventStore sqlConfig connectionPool

monadLoggerTracer :: Trace IO a -> Trace (TraceLoggerT IO) a
monadLoggerTracer = natTracer (\x -> TraceLoggerT $ const  x)
