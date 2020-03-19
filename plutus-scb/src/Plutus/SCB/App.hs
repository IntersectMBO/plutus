{-# LANGUAGE DerivingStrategies    #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns        #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE RecordWildCards       #-}

module Plutus.SCB.App where

import           Cardano.Node.API              (NodeFollowerAPI (..))
import qualified Cardano.Node.Client           as NodeClient
import qualified Cardano.Node.Server           as NodeServer
import qualified Cardano.SigningProcess.Client as SigningProcessClient
import qualified Cardano.SigningProcess.Server as SigningProcess
import qualified Cardano.Wallet.Client         as WalletClient
import qualified Cardano.Wallet.Server         as WalletServer
import           Control.Monad                 (void)
import           Control.Monad.Except          (ExceptT (ExceptT), MonadError, runExceptT, throwError)
import           Control.Monad.IO.Class        (MonadIO, liftIO)
import           Control.Monad.Logger          (LogLevel (LevelDebug), LoggingT, MonadLogger, filterLogger, logInfoN,
                                                runStdoutLoggingT)
import           Control.Monad.Reader          (MonadReader, ReaderT (ReaderT), asks, runReaderT)
import           Data.Aeson                    (FromJSON, ToJSON, eitherDecode)
import qualified Data.Aeson.Encode.Pretty      as JSON
import qualified Data.ByteString.Lazy.Char8    as BSL8
import qualified Data.Text                     as Text
import           Database.Persist.Sqlite       (retryOnBusy, runSqlPool)
import           Eventful                      (commandStoredAggregate, getLatestStreamProjection,
                                                serializedEventStoreWriter, serializedGlobalEventStoreReader,
                                                serializedVersionedEventStoreReader)
import           Eventful.Store.Sql            (jsonStringSerializer, sqlEventStoreReader, sqlGlobalEventStoreReader)
import           Eventful.Store.Sqlite         (initializeSqliteEventStore, sqliteEventStoreWriter)
import           Network.HTTP.Client           (defaultManagerSettings, newManager)
import           Plutus.SCB.Core               (Connection (Connection), ContractCommand (InitContract, UpdateContract),
                                                MonadContract, MonadEventStore, addProcessBus, dbConnect,
                                                invokeContract, refreshProjection, runCommand, toUUID)
import           Plutus.SCB.Types              (Config (Config), SCBError (ContractCommandError, NodeClientError, SigningProcessError, WalletClientError),
                                                dbConfig, nodeServerConfig, signingProcessConfig, walletServerConfig)
import           Servant.Client                (ClientEnv, ClientError, ClientM, mkClientEnv, runClientM)
import           System.Exit                   (ExitCode (ExitFailure, ExitSuccess))
import           System.Process                (readProcessWithExitCode)
import           Wallet.API                    (ChainIndexAPI, NodeAPI, SigningProcessAPI, WalletAPI, WalletDiagnostics,
                                                addSignatures, logMsg, ownOutputs, ownPubKey, slot, startWatching,
                                                submitTxn, updatePaymentWithChange, watchedAddresses)

------------------------------------------------------------
data Env =
    Env
        { dbConnection      :: Connection
        , walletClientEnv   :: ClientEnv
        , nodeClientEnv     :: ClientEnv
        , signingProcessEnv :: ClientEnv
        }

newtype App a =
    App
        { unApp :: ExceptT SCBError (ReaderT Env (LoggingT IO)) a
        }
    deriving newtype ( Functor
                     , Applicative
                     , Monad
                     , MonadLogger
                     , MonadIO
                     , MonadReader Env
                     , MonadError SCBError
                     )

instance NodeFollowerAPI App where
    subscribe = runNodeClientM NodeClient.newFollower
    blocks = runNodeClientM . NodeClient.getBlocks

instance NodeAPI App where
    submitTxn = void . runNodeClientM . NodeClient.addTx
    slot = runNodeClientM NodeClient.getCurrentSlot

instance WalletAPI App where
    ownPubKey = runWalletClientM WalletClient.getOwnPubKey
    updatePaymentWithChange _ _ = error "UNIMPLEMENTED: updatePaymentWithChange"
    ownOutputs = runWalletClientM WalletClient.getOwnOutputs

instance ChainIndexAPI App where
    watchedAddresses = runWalletClientM WalletClient.getWatchedAddresses
    startWatching = void . runWalletClientM . WalletClient.startWatching

instance SigningProcessAPI App where
    addSignatures sigs tx = runSigningProcessM (SigningProcessClient.addSignatures sigs tx)

runAppClientM ::
       (Env -> ClientEnv) -> (ClientError -> SCBError) -> ClientM a -> App a
runAppClientM f wrapErr action =
    App $ do
        env <- asks f
        result <- liftIO $ runClientM action env
        case result of
            Left err    -> throwError $ wrapErr err
            Right value -> pure value

runWalletClientM :: ClientM a -> App a
runWalletClientM = runAppClientM walletClientEnv WalletClientError

runNodeClientM :: ClientM a -> App a
runNodeClientM = runAppClientM nodeClientEnv NodeClientError

runSigningProcessM :: ClientM a -> App a
runSigningProcessM = runAppClientM signingProcessEnv SigningProcessError

runApp :: Config -> App a -> IO (Either SCBError a)
runApp Config {dbConfig, nodeServerConfig, walletServerConfig, signingProcessConfig} (App action) =
    runStdoutLoggingT . filterLogger (\_ level -> level > LevelDebug) $ do
        walletClientEnv <- mkEnv (WalletServer.baseUrl walletServerConfig)
        nodeClientEnv <- mkEnv (NodeServer.mscBaseUrl nodeServerConfig)
        signingProcessEnv <- mkEnv (SigningProcess.spBaseUrl signingProcessConfig)
        dbConnection <- runReaderT dbConnect dbConfig
        runReaderT (runExceptT action) $ Env {..}
  where
    mkEnv baseUrl = do
        manager <- liftIO $ newManager defaultManagerSettings
        pure $ mkClientEnv manager baseUrl

instance (FromJSON event, ToJSON event) => MonadEventStore event App where
    refreshProjection projection =
        App $ do
            (Connection (sqlConfig, connectionPool)) <- asks dbConnection
            let reader =
                    serializedGlobalEventStoreReader jsonStringSerializer $
                    sqlGlobalEventStoreReader sqlConfig
            ExceptT . fmap Right . flip runSqlPool connectionPool $
                getLatestStreamProjection reader projection
    runCommand aggregate source input =
        App $ do
            (Connection (sqlConfig, connectionPool)) <- asks dbConnection
            let reader =
                    serializedVersionedEventStoreReader jsonStringSerializer $
                    sqlEventStoreReader sqlConfig
            let writer =
                    addProcessBus
                        (serializedEventStoreWriter jsonStringSerializer $
                         sqliteEventStoreWriter sqlConfig)
                        reader
            ExceptT $
                fmap Right . retryOnBusy . flip runSqlPool connectionPool $
                commandStoredAggregate
                    writer
                    reader
                    aggregate
                    (toUUID source)
                    input

instance MonadContract App where
    invokeContract contractCommand =
        App $ do
            (exitCode, stdout, stderr) <-
                liftIO $
                case contractCommand of
                    InitContract contractPath ->
                        readProcessWithExitCode contractPath ["init"] ""
                    UpdateContract contractPath payload ->
                        readProcessWithExitCode
                            contractPath
                            ["update"]
                            (BSL8.unpack (JSON.encodePretty payload))
            case exitCode of
                ExitFailure code ->
                    pure . Left $ ContractCommandError code (Text.pack stderr)
                ExitSuccess ->
                    case eitherDecode (BSL8.pack stdout) of
                        Right value -> pure $ Right value
                        Left err ->
                            pure . Left $ ContractCommandError 0 (Text.pack err)

instance WalletDiagnostics App where
    logMsg = App . logInfoN

-- | Initialize/update the database to hold events.
migrate :: App ()
migrate =
    App $ do
        logInfoN "Migrating"
        Connection (sqlConfig, connectionPool) <- asks dbConnection
        ExceptT . fmap Right . flip runSqlPool connectionPool $
            initializeSqliteEventStore sqlConfig connectionPool
