{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns        #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeFamilies          #-}

module Plutus.SCB.Core
    ( migrate
    , simulate
    , dbStats
    , dbConnect
    , installContract
    , activateContract
    , reportContractStatus
    , installedContracts
    , installedContractsProjection
    , activeContracts
    , activeContractsProjection
    , activeContractHistory
    , Connection
    , MonadEventStore
    , refreshProjection
    , runGlobalQuery
    , runAggregateCommand
    , updateContract
    ) where

import           Control.Concurrent              (forkIO, myThreadId, threadDelay)
import           Control.Concurrent.Async        (concurrently_)
import           Control.Concurrent.STM          (TVar, atomically, newTVarIO, readTVarIO, writeTVar)
import           Control.Error.Util              (note)
import           Control.Monad                   (void, when)
import           Control.Monad.IO.Class          (MonadIO, liftIO)
import           Control.Monad.IO.Unlift         (MonadUnliftIO)
import           Control.Monad.Logger            (LoggingT, MonadLogger, logDebugN, logInfoN, runStdoutLoggingT)
import           Control.Monad.Reader            (MonadReader, ReaderT, ask, runReaderT)
import           Data.Aeson                      (FromJSON, ToJSON, eitherDecode, withObject, (.:))
import qualified Data.Aeson                      as JSON
import qualified Data.Aeson.Encode.Pretty        as JSON
import           Data.Aeson.Types                (Parser)
import qualified Data.Aeson.Types                as JSON
import qualified Data.ByteString.Lazy.Char8      as BSL8
import           Data.Map.Strict                 (Map)
import qualified Data.Map.Strict                 as Map
import           Data.Set                        (Set)
import qualified Data.Set                        as Set
import           Data.Text                       (Text)
import qualified Data.Text                       as Text
import qualified Data.UUID                       as UUID
import           Database.Persist.Sqlite         (ConnectionPool, createSqlitePoolFromInfo, mkSqliteConnectionInfo,
                                                  retryOnBusy, runSqlPool)
import           Eventful                        (Aggregate (Aggregate), EventStoreWriter, GlobalStreamProjection,
                                                  ProcessManager (ProcessManager), Projection,
                                                  StreamEvent (StreamEvent), UUID, VersionedEventStoreReader,
                                                  VersionedStreamEvent, aggregateCommandHandler, aggregateProjection,
                                                  applyProcessManagerCommandsAndEvents, commandStoredAggregate,
                                                  getLatestStreamProjection, globalStreamProjection, projectionMapMaybe,
                                                  serializedEventStoreWriter, serializedGlobalEventStoreReader,
                                                  serializedVersionedEventStoreReader, streamProjectionState,
                                                  synchronousEventBusWrapper, uuidNextRandom)
import           Eventful.Store.Sql              (JSONString, SqlEvent, SqlEventStoreConfig, defaultSqlEventStoreConfig,
                                                  jsonStringSerializer, sqlEventStoreReader, sqlGlobalEventStoreReader)
import           Eventful.Store.Sqlite           (initializeSqliteEventStore, sqliteEventStoreWriter)
import qualified Language.Plutus.Contract        as Contract
import           Options.Applicative.Help.Pretty (pretty, (<+>))
import           Plutus.SCB.Arbitrary            (genResponse)
import           Plutus.SCB.Command              (saveRequestResponseAggregate, saveTxAggregate)
import           Plutus.SCB.Events               (ChainEvent (UserEvent), EventId (EventId),
                                                  RequestEvent (CancelRequest, IssueRequest),
                                                  ResponseEvent (ResponseEvent), Tx,
                                                  UserEvent (ContractStateTransition, InstallContract))
import qualified Plutus.SCB.Events               as Events
import           Plutus.SCB.Query                (balances, eventCount, latestContractStatus, monoidProjection,
                                                  nullProjection, requestStats, setProjection, trialBalance)
import qualified Plutus.SCB.Relation             as Relation
import           Plutus.SCB.Types                (ActiveContract (ActiveContract),
                                                  ActiveContractState (ActiveContractState), Contract (Contract),
                                                  DbConfig (DbConfig), PartiallyDecodedResponse,
                                                  SCBError (ActiveContractStateNotFound, ContractCommandError, ContractNotFound, FileNotFound),
                                                  activeContract, activeContractId, activeContractPath, contractPath,
                                                  dbConfigFile, dbConfigPoolSize, hooks, newState,
                                                  partiallyDecodedResponse)
import           Plutus.SCB.Utils                (logInfoS, render, tshow)
import           System.Directory                (doesFileExist)
import           System.Exit                     (ExitCode (ExitFailure, ExitSuccess))
import           System.Process                  (readProcessWithExitCode)
import           Test.QuickCheck                 (arbitrary, frequency, generate)

data ThreadState
    = Running
    | Stopped
    deriving (Show, Eq)

newtype Connection =
    Connection (SqlEventStoreConfig SqlEvent JSONString, ConnectionPool)

-- | Initialize/update the database to hold events.
migrate :: (MonadUnliftIO m, MonadLogger m, MonadReader Connection m) => m ()
migrate = do
    logInfoN "Migrating"
    Connection (sqlConfig, connectionPool) <- ask
    initializeSqliteEventStore sqlConfig connectionPool

-- | A long-ish running process that fills the database with lots of event data.
simulate :: (MonadUnliftIO m, MonadLogger m, MonadReader Connection m) => m ()
simulate = do
    logInfoN "Simulating"
    connection <- ask
    runWriters connection

-- | Dump various statistics and reports from various queries over the event store database.
dbStats :: (MonadLogger m, MonadEventStore ChainEvent m) => m ()
dbStats = do
    logInfoN "Querying"
    reportTrialBalance
    reportClosingBalances
    reportEventCount
    reportRequestStats

------------------------------------------------------------
-- | Write lots of events into the store. At the moment this code
-- exercises the eventstore and the multi-threaded generation/storage of
-- events.
runWriters ::
       forall m. (MonadLogger m, MonadIO m)
    => Connection
    -> m ()
runWriters connection = do
    threadState <- liftIO $ newTVarIO Running
        --
    logInfoN "Started writers"
    let writerAction =
            runStdoutLoggingT . flip runReaderT connection $ do
                tx :: Tx <- liftIO $ generate arbitrary
                void $
                    runAggregateCommand
                        saveTxAggregate
                        (UUID.fromWords 0 0 0 1)
                        tx
                --
                requestId <- liftIO $ EventId <$> uuidNextRandom
                request <- liftIO $ generate arbitrary
                cancellation <-
                    liftIO $
                    generate $
                    frequency
                        [ (1, pure $ Just (CancelRequest requestId))
                        , (10, pure Nothing)
                        ]
                response <-
                    liftIO $
                    generate $
                    frequency
                        [ ( 10
                          , case genResponse request of
                                Nothing -> pure Nothing
                                Just generator ->
                                    Just . ResponseEvent requestId <$> generator)
                        , (1, pure Nothing)
                        ]
                me <- liftIO myThreadId
                logInfoN $ "(" <> tshow me <> ") Write"
                void $
                    runAggregateCommand
                        saveRequestResponseAggregate
                        (UUID.fromWords 0 0 0 2)
                        (IssueRequest requestId request, cancellation, response)
                liftIO pauseBeforeRepeat
        runWriterAction =
            void . forkIO $ repeatIOAction threadState writerAction
    liftIO $
        concurrently_
            (concurrently_ runWriterAction runWriterAction)
            (do pauseForWrites
                atomically $ writeTVar threadState Stopped)
    logInfoN "Stopped writers"
  where
    pauseForWrites = void $ threadDelay (5 * 60 * 1000 * 1000)
    pauseBeforeRepeat = void $ threadDelay (500 * 1000)

repeatIOAction :: TVar ThreadState -> IO a -> IO ()
repeatIOAction threadState action = go
  where
    go = do
        state <- readTVarIO threadState
        when (state == Running) $ do
            void action
            go

------------------------------------------------------------
reportTrialBalance :: (MonadLogger m, MonadEventStore ChainEvent m) => m ()
reportTrialBalance = do
    trialBalanceProjection <- runGlobalQuery trialBalance
    logInfoN "Trial Balance"
    logInfoS trialBalanceProjection

reportEventCount :: (MonadLogger m, MonadEventStore ChainEvent m) => m ()
reportEventCount = do
    eventCountProjection <- runGlobalQuery eventCount
    logInfoN $ "EventCount: " <> tshow eventCountProjection

reportRequestStats :: (MonadLogger m, MonadEventStore ChainEvent m) => m ()
reportRequestStats = do
    requestStatsProjection <- runGlobalQuery requestStats
    logInfoN $ render requestStatsProjection

reportClosingBalances :: (MonadLogger m, MonadEventStore ChainEvent m) => m ()
reportClosingBalances = do
    updatedProjection <- runGlobalQuery balances
    logInfoN "Closing Balances"
    let closingBalances = Relation.fromMap updatedProjection
    let report = (,) <$> Events.users <*> closingBalances
    logInfoS report

------------------------------------------------------------
withFile ::
       (MonadIO m) => (FilePath -> m b) -> FilePath -> m (Either SCBError b)
withFile action filePath = do
    exists <- liftIO $ doesFileExist filePath
    if not exists
        then pure $ Left $ FileNotFound filePath
        else Right <$> action filePath

installContract ::
       (MonadIO m, MonadLogger m, MonadEventStore ChainEvent m)
    => FilePath
    -> m (Either SCBError ())
installContract =
    withFile $ \filePath -> do
        logInfoN $ "Installing: " <> tshow filePath
        void $
            runAggregateCommand
                installCommand
                (UUID.fromWords 0 0 0 3)
                (Contract {contractPath = filePath})
        logInfoN "Installed."

installCommand :: Aggregate () ChainEvent Contract
installCommand =
    Aggregate
        { aggregateProjection = nullProjection
        , aggregateCommandHandler =
              \() contract -> [UserEvent $ InstallContract contract]
        }

activateContract ::
       (MonadLogger m, MonadEventStore ChainEvent m, MonadIO m)
    => FilePath
    -> m (Either SCBError ())
activateContract filePath = do
    logInfoN "Finding Contract"
    mContract <- lookupContract filePath
    activeContractId <- liftIO uuidNextRandom
    case mContract of
        Left err -> pure $ Left err
        Right contract -> do
            logInfoN "Initializing Contract"
            mResponse <- invokeContract $ InitContract contractPath
            case mResponse of
                Left err -> pure $ Left err
                Right response -> do
                    let activeContractState =
                            ActiveContractState
                                { activeContract =
                                      ActiveContract
                                          { activeContractId
                                          , activeContractPath =
                                                contractPath contract
                                          }
                                , partiallyDecodedResponse = response
                                }
                    logInfoN "Storing Initial Contract State"
                    void $
                        runAggregateCommand
                            saveContractState
                            (UUID.fromWords 0 0 0 3)
                            activeContractState
                    logInfoN . render $
                        "Installed:" <+>
                        pretty (activeContract activeContractState)
                    logInfoN "Done"
                    pure $ Right ()

updateContract ::
       (MonadLogger m, MonadEventStore ChainEvent m, MonadIO m)
    => UUID
    -> Text
    -> JSON.Value
    -> m (Either SCBError ())
updateContract uuid endpointName endpointPayload = do
    logInfoN "Finding Contract"
    mContract <- lookupActiveContractState uuid
    case mContract of
        Left err -> pure $ Left err
        Right oldContractState -> do
            logInfoN "Updating Contract"
            mResponse <-
                updateContract_ oldContractState endpointName endpointPayload
            case mResponse of
                Left err -> pure $ Left err
                Right response -> do
                    let updatedContractState =
                            oldContractState
                                {partiallyDecodedResponse = response}
                    logInfoN "Storing Updated Contract State"
                    logInfoN $
                        "UnbalancedTxs" <>
                        tshow
                            (JSON.parseEither
                                 parseUnbalancedTxKey
                                 (hooks response))
                    void $
                        runAggregateCommand
                            saveContractState
                            (UUID.fromWords 0 0 0 3)
                            updatedContractState
                    logInfoN . render $
                        "Updated:" <+> pretty updatedContractState
                    logInfoN "Done"
                    pure $ Right ()

parseUnbalancedTxKey :: JSON.Value -> Parser [Contract.UnbalancedTx]
parseUnbalancedTxKey = withObject "tx key" $ \o -> o .: "tx"

reportContractStatus ::
       (MonadLogger m, MonadEventStore ChainEvent m) => UUID -> m ()
reportContractStatus uuid = do
    logInfoN "Finding Contract"
    statuses <- runGlobalQuery latestContractStatus
    logInfoN $ render $ Map.lookup uuid statuses

lookupContract ::
       MonadEventStore ChainEvent m => FilePath -> m (Either SCBError Contract)
lookupContract filePath = do
    installed <- installedContracts
    let matchingContracts =
            Set.filter
                (\Contract {contractPath} -> contractPath == filePath)
                installed
    pure $ note (ContractNotFound filePath) $ Set.lookupMin matchingContracts

lookupActiveContractState ::
       MonadEventStore ChainEvent m
    => UUID
    -> m (Either SCBError ActiveContractState)
lookupActiveContractState uuid = do
    active <- activeContractStates
    pure $ note (ActiveContractStateNotFound uuid) $ Map.lookup uuid active

data ContractCommand
    = InitContract FilePath
    | UpdateContract FilePath JSON.Value
    deriving (Show, Eq)

invokeContract ::
       MonadIO m
    => ContractCommand
    -> m (Either SCBError PartiallyDecodedResponse)
invokeContract contractPath args stdin = do
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
                Left err    -> pure . Left $ ContractCommandError 0 (Text.pack err)

updateContract_ ::
       MonadIO m
    => ActiveContractState
    -> Text
    -> JSON.Value
    -> m (Either SCBError PartiallyDecodedResponse)
updateContract_ ActiveContractState { activeContract = ActiveContract {activeContractPath}
                                    , partiallyDecodedResponse
                                    } endpointName endpointPayload =
    invokeContract $
    Updatecontract activeContractPath $
    JSON.object
        [ ("oldState", newState partiallyDecodedResponse)
        , ( "event"
          , JSON.object
                [("tag", JSON.String endpointName), ("value", endpointPayload)])
        ]

saveContractState :: Aggregate () ChainEvent ActiveContractState
saveContractState =
    Aggregate {aggregateProjection = nullProjection, aggregateCommandHandler}
  where
    aggregateCommandHandler _ state =
        [UserEvent $ ContractStateTransition state]

installedContracts :: MonadEventStore ChainEvent m => m (Set Contract)
installedContracts = runGlobalQuery installedContractsProjection

installedContractsProjection ::
       Projection (Set Contract) (StreamEvent key position ChainEvent)
installedContractsProjection = projectionMapMaybe contractPaths setProjection
  where
    contractPaths (StreamEvent _ _ (UserEvent (InstallContract contract))) =
        Just contract
    contractPaths _ = Nothing

activeContracts :: MonadEventStore ChainEvent m => m (Set ActiveContract)
activeContracts = runGlobalQuery activeContractsProjection

activeContractsProjection ::
       Projection (Set ActiveContract) (StreamEvent key position ChainEvent)
activeContractsProjection = projectionMapMaybe contractPaths setProjection
  where
    contractPaths (StreamEvent _ _ (UserEvent (ContractStateTransition state))) =
        Just $ activeContract state
    contractPaths _ = Nothing

activeContractHistory ::
       MonadEventStore ChainEvent m => UUID -> m [ActiveContractState]
activeContractHistory uuid = runGlobalQuery activeContractHistoryProjection
  where
    activeContractHistoryProjection ::
           Projection [ActiveContractState] (StreamEvent key position ChainEvent)
    activeContractHistoryProjection =
        projectionMapMaybe contractPaths monoidProjection
      where
        contractPaths (StreamEvent _ _ (UserEvent (ContractStateTransition state))) =
            if activeContractId (activeContract state) == uuid
                then Just [state]
                else Nothing
        contractPaths _ = Nothing

activeContractStates ::
       MonadEventStore ChainEvent m => m (Map UUID ActiveContractState)
activeContractStates = runGlobalQuery activeContractStatesProjection
  where
    activeContractStatesProjection ::
           Projection (Map UUID ActiveContractState) (StreamEvent key position ChainEvent)
    activeContractStatesProjection =
        projectionMapMaybe contractStatePaths monoidProjection
      where
        contractStatePaths (StreamEvent _ _ (UserEvent (ContractStateTransition state))) =
            Just $ Map.singleton (activeContractId (activeContract state)) state
        contractStatePaths _ = Nothing

------------------------------------------------------------
-- | Create a database 'Connection' containing the connection pool
-- plus some configuration information.
dbConnect ::
       (MonadUnliftIO m, MonadLogger m, MonadReader DbConfig m) => m Connection
dbConnect = do
    DbConfig {dbConfigFile, dbConfigPoolSize} <- ask
    let connectionInfo = mkSqliteConnectionInfo dbConfigFile
    logDebugN "Connecting to DB"
    connectionPool <- createSqlitePoolFromInfo connectionInfo dbConfigPoolSize
    pure $ Connection (defaultSqlEventStoreConfig, connectionPool)

------------------------------------------------------------
-- TODO Perhaps we should change runAggregateCommand to take a closed list of sources, rather than any freeform UUID.
class Monad m =>
      MonadEventStore event m
    -- | Update a 'Projection'.
    where
    refreshProjection ::
           GlobalStreamProjection state event
        -> m (GlobalStreamProjection state event)
    -- | Update a command through an 'Aggregate'.
    runAggregateCommand ::
           Aggregate state event command -> UUID -> command -> m [event]

instance (FromJSON event, ToJSON event) =>
         MonadEventStore event (ReaderT Connection (LoggingT IO)) where
    refreshProjection projection = do
        (Connection (sqlConfig, connectionPool)) <- ask
        let reader =
                serializedGlobalEventStoreReader jsonStringSerializer $
                sqlGlobalEventStoreReader sqlConfig
        flip runSqlPool connectionPool $
            getLatestStreamProjection reader projection
    runAggregateCommand aggregate identifier input = do
        (Connection (sqlConfig, connectionPool)) <- ask
        let reader =
                serializedVersionedEventStoreReader jsonStringSerializer $
                sqlEventStoreReader sqlConfig
        let writer =
                addProcessBus
                    (serializedEventStoreWriter jsonStringSerializer $
                     sqliteEventStoreWriter sqlConfig)
                    reader
        retryOnBusy . flip runSqlPool connectionPool $
            commandStoredAggregate writer reader aggregate identifier input

runGlobalQuery ::
       MonadEventStore event m
    => Projection a (VersionedStreamEvent event)
    -> m a
runGlobalQuery query =
    fmap streamProjectionState <$> refreshProjection $
    globalStreamProjection query

addProcessBus ::
       Monad m
    => EventStoreWriter m event
    -> VersionedEventStoreReader m event
    -> EventStoreWriter m event
addProcessBus writer reader =
    synchronousEventBusWrapper
        writer
        [ \subwriter _ _ ->
              applyProcessManagerCommandsAndEvents
                  (ProcessManager nullProjection (\_ -> []) (\_ -> []))
                  subwriter
                  reader
                  ()
        ]
