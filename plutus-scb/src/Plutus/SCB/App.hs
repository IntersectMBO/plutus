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
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeOperators         #-}
{-# OPTIONS_GHC -fno-warn-partial-type-signatures #-}

module Plutus.SCB.App where

import           Cardano.ChainIndex.Client     (handleChainIndexClient)
import qualified Cardano.ChainIndex.Types      as ChainIndex
import           Cardano.Node.Client           (handleNodeClientClient, handleNodeFollowerClient, handleRandomTxClient)
import           Cardano.Node.Follower         (NodeFollowerEffect)
import           Cardano.Node.RandomTx         (GenRandomTx)
import qualified Cardano.Node.Server           as NodeServer
import qualified Cardano.SigningProcess.Client as SigningProcessClient
import qualified Cardano.SigningProcess.Server as SigningProcess
import qualified Cardano.Wallet.Client         as WalletClient
import qualified Cardano.Wallet.Server         as WalletServer
import           Control.Monad.Freer
import           Control.Monad.Freer.Error     (Error, handleError, runError, throwError)
import           Control.Monad.Freer.Extra.Log (Log, logDebug, logInfo, runStderrLog, writeToLog)
import           Control.Monad.Freer.Reader    (Reader, asks, runReader)
import           Control.Monad.Freer.Writer    (Writer)
import           Control.Monad.IO.Class        (MonadIO, liftIO)
import           Control.Monad.IO.Unlift       (MonadUnliftIO)
import           Control.Monad.Logger          (LogLevel, LoggingT (..), MonadLogger, filterLogger, runStdoutLoggingT)
import           Data.Aeson                    (FromJSON, eitherDecode)
import qualified Data.Aeson.Encode.Pretty      as JSON
import qualified Data.ByteString.Lazy.Char8    as BSL8
import qualified Data.Text                     as Text
import           Database.Persist.Sqlite       (runSqlPool)
import           Eventful.Store.Sqlite         (initializeSqliteEventStore)
import           Network.HTTP.Client           (defaultManagerSettings, newManager)
import           Plutus.SCB.Core               (Connection (Connection), ContractCommand (InitContract, UpdateContract),
                                                dbConnect)
import           Plutus.SCB.Effects.Contract   (ContractEffect (..))
import           Plutus.SCB.Effects.EventLog   (EventLogEffect (..), handleEventLogSql)
import           Plutus.SCB.Effects.UUID       (UUIDEffect, handleUUIDEffect)
import           Plutus.SCB.Events             (ChainEvent)
import           Plutus.SCB.Types              (Config (Config), ContractExe (..), SCBError (..), chainIndexConfig,
                                                dbConfig, nodeServerConfig, signingProcessConfig, walletServerConfig)
import           Servant.Client                (ClientEnv, ClientError, mkClientEnv)
import           System.Exit                   (ExitCode (ExitFailure, ExitSuccess))
import           System.Process                (readProcessWithExitCode)
import           Wallet.API                    (WalletAPIError)
import           Wallet.Effects                (ChainIndexEffect, NodeClientEffect, SigningProcessEffect, WalletEffect)
import qualified Wallet.Emulator.Wallet


------------------------------------------------------------
data Env =
    Env
        { dbConnection      :: Connection
        , walletClientEnv   :: ClientEnv
        , nodeClientEnv     :: ClientEnv
        , signingProcessEnv :: ClientEnv
        , chainIndexEnv     :: ClientEnv
        }

type AppBackend m =
        '[ GenRandomTx
         , NodeFollowerEffect
         , Error ClientError
         , WalletEffect
         , Error WalletAPIError
         , Error ClientError
         , NodeClientEffect
         , Error ClientError
         , SigningProcessEffect
         , Error ClientError
         , UUIDEffect
         , ContractEffect ContractExe
         , ChainIndexEffect
         , Error ClientError
         , EventLogEffect (ChainEvent ContractExe)
         , Error SCBError
         , Writer [Wallet.Emulator.Wallet.WalletEvent]
         , Log
         , Reader Connection
         , Reader Env
         , m
         ]

runAppBackend ::
    forall m a.
    ( MonadIO m
    , MonadLogger m
    , MonadUnliftIO m
    )
    => Env
    -> Eff (AppBackend m) a
    -> m (Either SCBError a)
runAppBackend e@Env{dbConnection, nodeClientEnv, walletClientEnv, signingProcessEnv, chainIndexEnv} =
    runM
    . runReader e
    . runReader dbConnection
    . runStderrLog
    . writeToLog
    . runError
    . handleEventLogSql
    . handleChainIndex
    . handleContractEffectApp
    . handleUUIDEffect
    . handleSigningProcess
    . handleNodeClient
    . handleWallet
    . handleNodeFollower
    . handleRandomTxClient nodeClientEnv
    where
        handleChainIndex :: Eff (ChainIndexEffect ': Error ClientError ': _) a -> Eff _ a
        handleChainIndex =
            flip handleError (throwError . ChainIndexError)
            . handleChainIndexClient chainIndexEnv

        handleSigningProcess :: Eff (SigningProcessEffect ': Error ClientError ': _) a -> Eff _ a
        handleSigningProcess =
            flip handleError (throwError . SigningProcessError)
            . SigningProcessClient.handleSigningProcessClient signingProcessEnv

        handleNodeClient :: Eff (NodeClientEffect ': Error ClientError ': _) a -> Eff _ a
        handleNodeClient =
            flip handleError (throwError . NodeClientError)
            . handleNodeClientClient nodeClientEnv

        handleNodeFollower :: Eff (NodeFollowerEffect ': Error ClientError ': _) a -> Eff _ a
        handleNodeFollower =
            flip handleError (throwError . NodeClientError)
            . handleNodeFollowerClient nodeClientEnv

        handleWallet :: Eff (WalletEffect ': Error WalletAPIError ': Error ClientError ': _) a -> Eff _ a
        handleWallet =
            flip handleError (throwError . WalletClientError)
            . flip handleError (throwError . WalletError)
            . WalletClient.handleWalletClient walletClientEnv


type App a = Eff (AppBackend (LoggingT IO)) a

runApp :: LogLevel -> Config -> App a -> IO (Either SCBError a)
runApp minLogLevel Config {dbConfig, nodeServerConfig, walletServerConfig, signingProcessConfig, chainIndexConfig} action =
    runStdoutLoggingT $ filterLogger (\_ logLevel -> logLevel >= minLogLevel) $ do
        walletClientEnv <- mkEnv (WalletServer.baseUrl walletServerConfig)
        nodeClientEnv <- mkEnv (NodeServer.mscBaseUrl nodeServerConfig)
        signingProcessEnv <- mkEnv (SigningProcess.spBaseUrl signingProcessConfig)
        chainIndexEnv <- mkEnv (ChainIndex.ciBaseUrl chainIndexConfig)
        dbConnection <- dbConnect dbConfig
        let env = Env {..}
        runAppBackend @(LoggingT IO) env action
  where
    mkEnv baseUrl =
            mkClientEnv
                <$> liftIO (newManager defaultManagerSettings)
                <*> pure baseUrl

handleContractEffectApp ::
       (Member Log effs, Member (Error SCBError) effs, LastMember m effs, MonadIO m)
    => Eff (ContractEffect ContractExe ': effs) ~> Eff effs
handleContractEffectApp =
    interpret $ \case
        InvokeContract contractCommand ->
            liftProcess $
            case contractCommand of
                InitContract (ContractExe contractPath) ->
                    readProcessWithExitCode contractPath ["init"] ""
                UpdateContract (ContractExe contractPath) payload ->
                    readProcessWithExitCode
                        contractPath
                        ["update"]
                        (BSL8.unpack (JSON.encodePretty payload))
        ExportSchema (ContractExe contractPath) ->
            liftProcess $
            readProcessWithExitCode contractPath ["export-signature"] ""

liftProcess ::
       (LastMember m effs, MonadIO m, FromJSON b, Member Log effs, Member (Error SCBError) effs)
    => IO (ExitCode, String, String)
    -> Eff effs b
liftProcess process = do
    (exitCode, stdout, stderr) <- sendM $ liftIO process
    case exitCode of
        ExitFailure code ->
            throwError $ ContractCommandError code (Text.pack stderr)
        ExitSuccess -> do
            logDebug $ "Response: " <> Text.pack stdout
            case eitherDecode (BSL8.pack stdout) of
                Right value -> pure value
                Left err    -> throwError $ ContractCommandError 0 (Text.pack err)

-- | Initialize/update the database to hold events.
migrate :: App ()
migrate = do
    logInfo "Migrating"
    Connection (sqlConfig, connectionPool) <- asks dbConnection
    liftIO
        $ flip runSqlPool connectionPool
        $ initializeSqliteEventStore sqlConfig connectionPool
