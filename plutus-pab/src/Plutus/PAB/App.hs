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
    StorageBackend(..),
    -- * App actions
    migrate,
    dbConnect,
    handleContractDefinition
    ) where

import           Cardano.Api.NetworkId.Extra                    (NetworkIdWrapper (..))
import           Cardano.BM.Trace                               (Trace, logDebug)
import qualified Cardano.ChainIndex.Types                       as ChainIndex
import           Cardano.Node.Client                            (handleNodeClientClient)
import qualified Cardano.Node.Client                            as NodeClient
import           Cardano.Node.Types                             (MockServerConfig (..))
import qualified Cardano.Protocol.Socket.Mock.Client            as MockClient
import qualified Cardano.Wallet.Mock.Client                     as WalletClient
import qualified Cardano.Wallet.Mock.Types                      as Wallet
import qualified Control.Concurrent.STM                         as STM
import           Control.Monad.Freer
import           Control.Monad.Freer.Error                      (handleError, throwError)
import           Control.Monad.Freer.Extras.Log                 (mapLog)
import           Control.Monad.IO.Class                         (MonadIO (..))
import           Data.Aeson                                     (FromJSON, ToJSON)
import           Data.Coerce                                    (coerce)
import           Data.Text                                      (Text, pack, unpack)
import           Data.Typeable                                  (Typeable)
import           Database.Beam.Migrate.Simple
import qualified Database.Beam.Sqlite                           as Sqlite
import qualified Database.Beam.Sqlite.Migrate                   as Sqlite
import           Database.SQLite.Simple                         (open)
import qualified Database.SQLite.Simple                         as Sqlite
import           Network.HTTP.Client                            (managerModifyRequest, newManager,
                                                                 setRequestIgnoreStatus)
import           Network.HTTP.Client.TLS                        (tlsManagerSettings)
import qualified Plutus.ChainIndex.Client                       as ChainIndex
import           Plutus.PAB.Core                                (EffectHandlers (..), PABAction)
import qualified Plutus.PAB.Core                                as Core
import qualified Plutus.PAB.Core.ContractInstance.BlockchainEnv as BlockchainEnv
import           Plutus.PAB.Core.ContractInstance.STM           as Instances
import qualified Plutus.PAB.Db.Beam.ContractStore               as BeamEff
import           Plutus.PAB.Db.Memory.ContractStore             (InMemInstances, initialInMemInstances)
import qualified Plutus.PAB.Db.Memory.ContractStore             as InMem
import           Plutus.PAB.Effects.Contract                    (ContractDefinition (..))
import           Plutus.PAB.Effects.Contract.Builtin            (Builtin, BuiltinHandler (..), HasDefinitions (..))
import           Plutus.PAB.Effects.DbStore                     (checkedSqliteDb, handleDbStore)
import           Plutus.PAB.Monitoring.Monitoring               (handleLogMsgTrace)
import           Plutus.PAB.Monitoring.PABLogMsg                (PABLogMsg (..), PABMultiAgentMsg (UserLog))
import           Plutus.PAB.Timeout                             (Timeout (..))
import           Plutus.PAB.Types                               (Config (Config), DbConfig (..), PABError (..),
                                                                 WebserverConfig (..), chainIndexConfig, dbConfig,
                                                                 endpointTimeout, nodeServerConfig, pabWebserverConfig,
                                                                 walletServerConfig)
import           Servant.Client                                 (ClientEnv, mkClientEnv)

------------------------------------------------------------

-- | Application environment with a contract type `a`.
data AppEnv a =
    AppEnv
        { dbConnection          :: Sqlite.Connection
        , walletClientEnv       :: ClientEnv
        , nodeClientEnv         :: ClientEnv
        , chainIndexEnv         :: ClientEnv
        , txSendHandle          :: MockClient.TxSendHandle
        , chainSyncHandle       :: NodeClient.ChainSyncHandle
        , appConfig             :: Config
        , appTrace              :: Trace IO (PABLogMsg (Builtin a))
        , appInMemContractStore :: InMemInstances (Builtin a)
        }

appEffectHandlers
  :: forall a.
  ( FromJSON a
  , ToJSON a
  , HasDefinitions a
  , Typeable a
  )
  => StorageBackend
  -> Config
  -> Trace IO (PABLogMsg (Builtin a))
  -> BuiltinHandler a
  -> EffectHandlers (Builtin a) (AppEnv a)
appEffectHandlers storageBackend config trace BuiltinHandler{contractHandler} =
    EffectHandlers
        { initialiseEnvironment = do
            env <- liftIO $ mkEnv trace config
            let Config{nodeServerConfig=MockServerConfig{mscSocketPath, mscSlotConfig, mscNodeMode, mscNetworkId=NetworkIdWrapper networkId}} = config
            instancesState <- liftIO $ STM.atomically Instances.emptyInstancesState
            blockchainEnv <- liftIO $ BlockchainEnv.startNodeClient mscSocketPath mscNodeMode mscSlotConfig networkId instancesState
            pure (instancesState, blockchainEnv, env)

        , handleLogMessages =
            interpret (handleLogMsgTrace trace)
            . reinterpret (mapLog SMultiAgent)

        , handleContractEffect =
            interpret (handleLogMsgTrace trace)
            . reinterpret contractHandler

        , handleContractStoreEffect =
          case storageBackend of
            InMemoryBackend ->
              interpret (Core.handleUserEnvReader @(Builtin a) @(AppEnv a))
              . interpret (Core.handleMappedReader @(AppEnv a) appInMemContractStore)
              . reinterpret2 InMem.handleContractStore

            BeamSqliteBackend ->
              interpret (handleLogMsgTrace trace)
              . reinterpret (mapLog @_ @(PABLogMsg (Builtin a)) SMultiAgent)
              . interpret (Core.handleUserEnvReader @(Builtin a) @(AppEnv a))
              . interpret (Core.handleMappedReader @(AppEnv a) dbConnection)
              . interpret (handleDbStore trace)
              . reinterpretN @'[_, _, _, _] BeamEff.handleContractStore

        , handleContractDefinitionEffect =
            interpret (handleLogMsgTrace trace)
            . reinterpret (mapLog @_ @(PABLogMsg (Builtin a)) SMultiAgent)
            . interpret (Core.handleUserEnvReader @(Builtin a) @(AppEnv a))
            . interpret (Core.handleMappedReader @(AppEnv a) dbConnection)
            . interpret (handleDbStore trace)
            . reinterpretN @'[_, _, _, _] handleContractDefinition

        , handleServicesEffects = \wallet ->
            -- handle 'NodeClientEffect'
            flip handleError (throwError . NodeClientError)
            . interpret (Core.handleUserEnvReader @(Builtin a) @(AppEnv a))
            . reinterpret (Core.handleMappedReader @(AppEnv a) @NodeClient.ChainSyncHandle chainSyncHandle)
            . interpret (Core.handleUserEnvReader @(Builtin a) @(AppEnv a))
            . reinterpret (Core.handleMappedReader @(AppEnv a) @MockClient.TxSendHandle txSendHandle)
            . interpret (Core.handleUserEnvReader @(Builtin a) @(AppEnv a))
            . reinterpret (Core.handleMappedReader @(AppEnv a) @ClientEnv nodeClientEnv)
            . reinterpretN @'[_, _, _, _] (handleNodeClientClient @IO $ mscSlotConfig $ nodeServerConfig config)

            -- handle 'ChainIndexEffect'
            . flip handleError (throwError . ChainIndexError)
            . interpret (Core.handleUserEnvReader @(Builtin a) @(AppEnv a))
            . reinterpret (Core.handleMappedReader @(AppEnv a) @ClientEnv chainIndexEnv)
            . reinterpret2 (ChainIndex.handleChainIndexClient @IO)

            -- handle 'WalletEffect'
            . flip handleError (throwError . WalletClientError)
            . flip handleError (throwError . WalletError)
            . interpret (Core.handleUserEnvReader @(Builtin a) @(AppEnv a))
            . reinterpret (Core.handleMappedReader @(AppEnv a) @ClientEnv walletClientEnv)
            . reinterpretN @'[_, _, _] (WalletClient.handleWalletClient @IO wallet)

        , onStartup = pure ()

        , onShutdown = pure ()
        }

runApp ::
    forall a b.
    ( FromJSON a
    , ToJSON a
    , HasDefinitions a
    , Typeable a
    )
    => StorageBackend
    -> Trace IO (PABLogMsg (Builtin a)) -- ^ Top-level tracer
    -> BuiltinHandler a
    -> Config -- ^ Client configuration
    -> App a b -- ^ Action
    -> IO (Either PABError b)
runApp storageBackend trace contractHandler config@Config{pabWebserverConfig=WebserverConfig{endpointTimeout}} = Core.runPAB (Timeout endpointTimeout) (appEffectHandlers storageBackend config trace contractHandler)

type App a b = PABAction (Builtin a) (AppEnv a) b

data StorageBackend = BeamSqliteBackend | InMemoryBackend
  deriving (Eq, Ord, Show)

mkEnv :: Trace IO (PABLogMsg (Builtin a)) -> Config -> IO (AppEnv a)
mkEnv appTrace appConfig@Config { dbConfig
             , nodeServerConfig =  MockServerConfig{mscBaseUrl, mscSocketPath, mscSlotConfig}
             , walletServerConfig
             , chainIndexConfig
             } = do
    walletClientEnv <- clientEnv (Wallet.baseUrl walletServerConfig)
    nodeClientEnv <- clientEnv mscBaseUrl
    chainIndexEnv <- clientEnv (ChainIndex.ciBaseUrl chainIndexConfig)
    dbConnection <- dbConnect appTrace dbConfig
    txSendHandle <- liftIO $ MockClient.runTxSender mscSocketPath
    -- This is for access to the slot number in the interpreter
    chainSyncHandle <- Left <$> (liftIO $ MockClient.runChainSync' mscSocketPath mscSlotConfig)
    appInMemContractStore <- liftIO initialInMemInstances
    pure AppEnv {..}
  where
    clientEnv baseUrl = mkClientEnv <$> liftIO mkManager <*> pure (coerce baseUrl)

    mkManager =
        newManager $
        tlsManagerSettings {managerModifyRequest = pure . setRequestIgnoreStatus}

logDebugString :: Trace IO (PABLogMsg t) -> Text -> IO ()
logDebugString trace = logDebug trace . SMultiAgent . UserLog

-- | Initialize/update the database to hold our effects.
migrate :: Trace IO (PABLogMsg (Builtin a)) -> DbConfig -> IO ()
migrate trace config = do
    connection <- dbConnect trace config
    logDebugString trace "Running beam migration"
    runBeamMigration trace connection

runBeamMigration
  :: Trace IO (PABLogMsg (Builtin a))
  -> Sqlite.Connection
  -> IO ()
runBeamMigration trace conn = Sqlite.runBeamSqliteDebug (logDebugString trace . pack) conn $ do
  autoMigrate Sqlite.migrationBackend checkedSqliteDb

-- | Connect to the database.
dbConnect :: Trace IO (PABLogMsg (Builtin a)) -> DbConfig -> IO Sqlite.Connection
dbConnect trace DbConfig {dbConfigFile} = do
  logDebugString trace $ "Connecting to DB: " <> dbConfigFile
  open (unpack dbConfigFile)

handleContractDefinition ::
  forall a effs. HasDefinitions a
  => ContractDefinition (Builtin a)
  ~> Eff effs
handleContractDefinition = \case
  AddDefinition _ -> pure ()
  GetDefinitions  -> pure getDefinitions
