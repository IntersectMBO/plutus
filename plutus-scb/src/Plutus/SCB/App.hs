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
{-# LANGUAGE StrictData            #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeOperators         #-}
{-# OPTIONS_GHC -fno-warn-partial-type-signatures #-}

module Plutus.SCB.App where

import           Cardano.ChainIndex.Client        (handleChainIndexClient)
import qualified Cardano.ChainIndex.Types         as ChainIndex
import           Cardano.Node.Client              (handleNodeClientClient, handleNodeFollowerClient,
                                                   handleRandomTxClient)
import           Cardano.Node.Follower            (NodeFollowerEffect)
import           Cardano.Node.RandomTx            (GenRandomTx)
import qualified Cardano.Node.Server              as NodeServer
import qualified Cardano.SigningProcess.Client    as SigningProcessClient
import qualified Cardano.SigningProcess.Server    as SigningProcess
import qualified Cardano.Wallet.Client            as WalletClient
import qualified Cardano.Wallet.Server            as WalletServer
import           Control.Monad.Freer
import           Control.Monad.Freer.Error        (Error, handleError, runError, throwError)
import           Control.Monad.Freer.Extra.Log    (LogMsg, handleWriterLog, logDebug, logInfo, runStderrLog)
import           Control.Monad.Freer.Log          (LogMessage, LogObserve, handleObserveLog, renderLogMessages)
import qualified Control.Monad.Freer.Log          as Log
import           Control.Monad.Freer.Reader       (Reader, asks, runReader)
import           Control.Monad.Freer.WebSocket    (WebSocketEffect, handleWebSocket)
import           Control.Monad.Freer.Writer       (Writer)
import           Control.Monad.IO.Class           (MonadIO, liftIO)
import           Control.Monad.IO.Unlift          (MonadUnliftIO)
import           Control.Monad.Logger             (LogLevel, LoggingT (..), MonadLogger, filterLogger,
                                                   runStdoutLoggingT)
import           Data.Aeson                       (FromJSON, eitherDecode)
import qualified Data.Aeson                       as JSON
import qualified Data.Aeson.Encode.Pretty         as JSON
import qualified Data.ByteString.Lazy.Char8       as BSL8
import           Data.String                      (IsString (fromString))
import qualified Data.Text                        as Text
import qualified Data.Text.Encoding               as Text
import           Data.Text.Prettyprint.Doc        (Doc, Pretty (..), hang, viaShow, vsep, (<+>))
import           Data.Void                        (Void, absurd)
import           Database.Persist.Sqlite          (runSqlPool)
import           Eventful.Store.Sqlite            (initializeSqliteEventStore)
import           Language.Plutus.Contract.State   (ContractRequest)
import           Network.HTTP.Client              (defaultManagerSettings, newManager)
import           Plutus.SCB.Core                  (Connection (Connection),
                                                   ContractCommand (InitContract, UpdateContract), CoreMsg, dbConnect)
import           Plutus.SCB.Core.ContractInstance (ContractInstanceMsg)
import           Plutus.SCB.Effects.Contract      (ContractEffect (..))
import           Plutus.SCB.Effects.EventLog      (EventLogEffect (..), handleEventLogSql)
import           Plutus.SCB.Effects.UUID          (UUIDEffect, handleUUIDEffect)
import           Plutus.SCB.Events                (ChainEvent)
import           Plutus.SCB.Types                 (Config (Config), ContractExe (..), SCBError (..), chainIndexConfig,
                                                   dbConfig, nodeServerConfig, signingProcessConfig, walletServerConfig)
import           Plutus.SCB.Webserver.Types       (WebSocketLogMsg)
import           Servant.Client                   (ClientEnv, ClientError, mkClientEnv)
import           System.Exit                      (ExitCode (ExitFailure, ExitSuccess))
import           System.Process                   (readProcessWithExitCode)
import           Wallet.API                       (WalletAPIError)
import           Wallet.Effects                   (ChainIndexEffect, NodeClientEffect, SigningProcessEffect,
                                                   WalletEffect)
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
         , WebSocketEffect
         , Error SCBError
         , Writer [Wallet.Emulator.Wallet.WalletEvent]
         , LogMsg Wallet.Emulator.Wallet.WalletEvent
         , LogMsg ContractExeLogMsg
         , LogMsg (ContractInstanceMsg ContractExe)
         , LogMsg WebSocketLogMsg
         , LogMsg UnStringifyJSONLog
         , LogMsg (CoreMsg ContractExe)
         , LogObserve (LogMessage Text.Text)
         , LogMsg Text.Text
         , Reader Connection
         , Reader Config
         , Reader Env
         , m
         ]

runAppBackend ::
       forall m a. (MonadIO m, MonadLogger m, MonadUnliftIO m)
    => Config
    -> Eff (AppBackend m) a
    -> m (Either SCBError a)
runAppBackend config eff = do
    env@Env { dbConnection
            , nodeClientEnv
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
     . runStderrLog
     . handleObserveLog
     . renderLogMessages
     . renderLogMessages
     . renderLogMessages
     . renderLogMessages
     . renderLogMessages
     . renderLogMessages
     . handleWriterLog (\_ -> Log.Info)
     . runError
     . handleWebSocket
     . handleEventLogSql
     . handleChainIndex
     . handleContractEffectApp
     . handleUUIDEffect
     . handleSigningProcess
     . handleNodeClient
     . handleWallet
     . handleNodeFollower
     . handleRandomTxClient nodeClientEnv $ eff

type App a = Eff (AppBackend (LoggingT IO)) a

mkEnv :: (MonadUnliftIO m, MonadLogger m) => Config -> m Env
mkEnv Config { dbConfig
             , nodeServerConfig
             , walletServerConfig
             , signingProcessConfig
             , chainIndexConfig
             } = do
    walletClientEnv <- clientEnv (WalletServer.baseUrl walletServerConfig)
    nodeClientEnv <- clientEnv (NodeServer.mscBaseUrl nodeServerConfig)
    signingProcessEnv <-
        clientEnv (SigningProcess.spBaseUrl signingProcessConfig)
    chainIndexEnv <- clientEnv (ChainIndex.ciBaseUrl chainIndexConfig)
    dbConnection <- dbConnect dbConfig
    pure Env {..}
  where
    clientEnv baseUrl =
        mkClientEnv <$> liftIO (newManager defaultManagerSettings) <*>
        pure baseUrl

runApp :: LogLevel -> Config -> App a -> IO (Either SCBError a)
runApp minLogLevel config action =
    runStdoutLoggingT $
    filterLogger (\_ logLevel -> logLevel >= minLogLevel) $
    runAppBackend @(LoggingT IO) config action

data ContractExeLogMsg =
    InvokeContractMsg
    | InitContractMsg FilePath
    | UpdateContractMsg FilePath (ContractRequest JSON.Value)
    | ExportSignatureMsg FilePath
    | ProcessExitFailure String
    | ContractResponse String
    | Migrating
    | InvokingEndpoint String JSON.Value
    | EndpointInvocationResponse [Doc Void]
    | ContractExeSCBError SCBError

instance Pretty ContractExeLogMsg where
    pretty = \case
        InvokeContractMsg -> "InvokeContract"
        InitContractMsg fp -> fromString fp <+> "init"
        UpdateContractMsg fp vl ->
            let pl = BSL8.unpack (JSON.encodePretty vl) in
            fromString fp
            <+> "update"
            <+> fromString pl
        ExportSignatureMsg fp -> fromString fp <+> "export-signature"
        ProcessExitFailure err -> "ExitFailure" <+> pretty err
        ContractResponse str -> pretty str
        Migrating -> "Migrating"
        InvokingEndpoint s v ->
            "Invoking:" <+> pretty s <+> "/" <+> viaShow v
        EndpointInvocationResponse v ->
            hang 2 $ vsep ("Invocation response:" : fmap (fmap absurd) v)
        ContractExeSCBError e ->
            "SCB error:" <+> pretty e

handleContractEffectApp ::
       (Member (LogMsg ContractExeLogMsg) effs, Member (Error SCBError) effs, LastMember m effs, MonadIO m)
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
       (LastMember m effs, MonadIO m, FromJSON b, Member (LogMsg ContractExeLogMsg) effs, Member (Error SCBError) effs)
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

data UnStringifyJSONLog =
    ParseStringifiedJSONAttempt
    | ParseStringifiedJSONFailed
    | ParseStringifiedJSONSuccess

instance Pretty UnStringifyJSONLog where
    pretty = \case
        ParseStringifiedJSONAttempt -> "parseStringifiedJSON: Attempting to remove 1 layer StringifyJSON"
        ParseStringifiedJSONFailed -> "parseStringifiedJSON: Failed, returning original string"
        ParseStringifiedJSONSuccess -> "parseStringifiedJSON: Succeeded"

parseStringifiedJSON ::
    forall effs.
    Member (LogMsg UnStringifyJSONLog) effs
    => JSON.Value
    -> Eff effs JSON.Value
parseStringifiedJSON v = case v of
    JSON.String s -> do
        logDebug ParseStringifiedJSONAttempt
        let s' = JSON.decode @JSON.Value $ BSL8.fromStrict $ Text.encodeUtf8 s
        case s' of
            Nothing -> do
                logDebug ParseStringifiedJSONFailed
                pure v
            Just s'' -> do
                logDebug ParseStringifiedJSONSuccess
                pure s''
    _ -> pure v
