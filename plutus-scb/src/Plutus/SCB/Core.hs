{-# LANGUAGE DeriveAnyClass      #-}
{-# LANGUAGE DerivingStrategies  #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE NamedFieldPuns      #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies        #-}

module Plutus.SCB.Core
    ( migrate
    , simulate
    , dbStats
    , DbConfig
    ) where

import           Control.Concurrent       (forkIO, myThreadId, threadDelay)
import           Control.Concurrent.Async (concurrently_)
import           Control.Concurrent.STM   (TVar, atomically, newTVarIO, readTVarIO, writeTVar)
import           Control.Monad            (void, when)
import           Control.Monad.IO.Class   (MonadIO, liftIO)
import           Control.Monad.IO.Unlift  (MonadUnliftIO)
import           Control.Monad.Logger     (MonadLogger, logDebugN, logInfoN, runStderrLoggingT)
import           Control.Monad.Reader     (MonadReader, ask, runReaderT)
import           Data.Aeson               (FromJSON, ToJSON)
import           Data.Map                 (Map)
import           Data.Text                (Text)
import qualified Data.UUID                as UUID
import           Database.Persist.Sqlite  (ConnectionPool, SqlPersistT, createSqlitePoolFromInfo,
                                           mkSqliteConnectionInfo, retryOnBusy, runSqlPool)
import           Eventful                 (Aggregate, GlobalStreamProjection, UUID, commandStoredAggregate,
                                           getLatestStreamProjection, globalStreamProjection,
                                           serializedEventStoreWriter, serializedGlobalEventStoreReader,
                                           serializedVersionedEventStoreReader, streamProjectionState, uuidNextRandom)
import           Eventful.Store.Sql       (JSONString, SqlEvent, SqlEventStoreConfig, defaultSqlEventStoreConfig,
                                           jsonStringSerializer, sqlEventStoreReader, sqlGlobalEventStoreReader)
import           Eventful.Store.Sqlite    (initializeSqliteEventStore, sqliteEventStoreWriter)
import           GHC.Generics             (Generic)
import           Ledger.Value             (Value)
import           Plutus.SCB.Arbitrary     (genResponse)
import           Plutus.SCB.Command       (saveRequestResponseAggregate, saveTxAggregate)
import           Plutus.SCB.Events        (AccountId, ChainEvent, EventId (EventId),
                                           RequestEvent (CancelRequest, IssueRequest), ResponseEvent (ResponseEvent),
                                           Tx)
import qualified Plutus.SCB.Events        as Events
import           Plutus.SCB.Query         (RequestStats, balances, eventCount, requestStats, trialBalance)
import qualified Plutus.SCB.Relation      as Relation
import           Plutus.SCB.Utils         (logInfoS, render, tshow)
import           Test.QuickCheck          (arbitrary, frequency, generate)

data ThreadState
    = Running
    | Stopped
    deriving (Show, Eq)

data DbConfig =
    DbConfig
        { dbConfigFile     :: Text
        -- ^ The path to the sqlite database file. May be absolute or relative.
        , dbConfigPoolSize :: Int
        -- ^ Max number of concurrent sqlite database connections.
        }
    deriving (Show, Eq, Generic, FromJSON)

newtype Connection =
    Connection (SqlEventStoreConfig SqlEvent JSONString, ConnectionPool)

-- | Initialize/update the database to hold events.
migrate :: (MonadUnliftIO m, MonadLogger m, MonadReader DbConfig m) => m ()
migrate = do
    logInfoN "Migrating"
    Connection (sqlConfig, connectionPool) <- dbConnect
    initializeSqliteEventStore sqlConfig connectionPool

-- | A long-ish running process that fills the database with lots of event data.
simulate :: (MonadUnliftIO m, MonadLogger m, MonadReader DbConfig m) => m ()
simulate = do
    logInfoN "Simulating"
    connection <- dbConnect
    runWriters connection

-- | Dump various statistics and reports from various queries over the event store database.
dbStats :: (MonadUnliftIO m, MonadLogger m, MonadReader DbConfig m) => m ()
dbStats = do
    logInfoN "Querying"
    connection <- dbConnect
    flip runReaderT connection $ do
        void reportTrialBalance
        void reportClosingBalances
        void reportEventCount
        void reportRequestStats

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
            flip runReaderT connection $
            runStderrLoggingT $ do
                tx :: Tx <- liftIO $ generate arbitrary
                void . retryOnBusy $
                    runCommand saveTxAggregate (UUID.fromWords 0 0 0 1) tx
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
                void . retryOnBusy $
                    runCommand
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
reportTrialBalance ::
       (MonadLogger m, MonadIO m, MonadReader Connection m)
    => m (GlobalStreamProjection Value ChainEvent)
reportTrialBalance = do
    trialBalanceProjection <-
        refreshProjection $ globalStreamProjection trialBalance
    logInfoN "Trial Balance"
    logInfoS $ streamProjectionState trialBalanceProjection
    pure trialBalanceProjection

reportEventCount ::
       (MonadLogger m, MonadIO m, MonadReader Connection m)
    => m (GlobalStreamProjection Int ChainEvent)
reportEventCount = do
    eventCountProjection <-
        refreshProjection $ globalStreamProjection eventCount
    logInfoN "EventCount"
    logInfoN $ render eventCountProjection
    pure eventCountProjection

reportRequestStats ::
       (MonadLogger m, MonadIO m, MonadReader Connection m)
    => m (GlobalStreamProjection RequestStats ChainEvent)
reportRequestStats = do
    requestStatsProjection <-
        refreshProjection $ globalStreamProjection requestStats
    logInfoN $ render requestStatsProjection
    pure requestStatsProjection

reportClosingBalances ::
       (MonadLogger m, MonadIO m, MonadReader Connection m)
    => m (GlobalStreamProjection (Map AccountId Value) ChainEvent)
reportClosingBalances = do
    updatedProjection <- refreshProjection $ globalStreamProjection balances
    logInfoN "Closing Balances"
    let closingBalances =
            Relation.fromMap $ streamProjectionState updatedProjection
    let report = (,) <$> Events.users <*> closingBalances
    logInfoS report
    pure updatedProjection

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

runDbTx :: MonadIO m => ConnectionPool -> SqlPersistT IO a -> m a
runDbTx connectionPool = liftIO . flip runSqlPool connectionPool

-- | Update a 'Projection'.
refreshProjection ::
       (FromJSON event, ToJSON event, MonadIO m, MonadReader Connection m)
    => GlobalStreamProjection state event
    -> m (GlobalStreamProjection state event)
refreshProjection projection = do
    (Connection (sqlConfig, connectionPool)) <- ask
    let serializedGlobalReader =
            serializedGlobalEventStoreReader jsonStringSerializer $
            sqlGlobalEventStoreReader sqlConfig
    runDbTx connectionPool $
        getLatestStreamProjection serializedGlobalReader projection

-- | Update a command through an 'Aggregate'.
runCommand ::
       (MonadIO m, ToJSON event, FromJSON event, MonadReader Connection m)
    => Aggregate state event command
    -> UUID
    -> command
    -> m [event]
runCommand aggregate identifier input = do
    (Connection (sqlConfig, connectionPool)) <- ask
    runDbTx connectionPool $
        commandStoredAggregate
            (serializedEventStoreWriter jsonStringSerializer $
             sqliteEventStoreWriter sqlConfig)
            (serializedVersionedEventStoreReader jsonStringSerializer $
             sqlEventStoreReader sqlConfig)
            aggregate
            identifier
            input
