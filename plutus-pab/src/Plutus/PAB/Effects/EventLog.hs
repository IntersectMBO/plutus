{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs            #-}
{-# LANGUAGE LambdaCase       #-}
{-# LANGUAGE RankNTypes       #-}
{-# LANGUAGE TemplateHaskell  #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators    #-}

module Plutus.PAB.Effects.EventLog where

import           Cardano.BM.Trace                        (Trace)
import           Control.Concurrent.STM                  (TVar)
import qualified Control.Concurrent.STM                  as STM
import           Control.Monad.Freer                     (Eff, LastMember, Member, sendM, type (~>))
import           Control.Monad.Freer.Reader              (Reader, ask)
import           Control.Monad.Freer.TH                  (makeEffect)
import           Control.Monad.IO.Class                  (MonadIO (..))
import           Data.Aeson                              (FromJSON, ToJSON)
import           Database.Persist.Sqlite                 (ConnectionPool, SqlPersistT, retryOnBusy, runSqlPool)
import           Eventful                                (Aggregate, EventStoreWriter, GlobalStreamProjection,
                                                          Projection, VersionedEventStoreReader, VersionedStreamEvent,
                                                          commandStoredAggregate, getLatestStreamProjection,
                                                          globalStreamProjection, serializedEventStoreWriter,
                                                          serializedGlobalEventStoreReader,
                                                          serializedVersionedEventStoreReader, streamProjectionState)
import qualified Eventful.Store.Memory                   as M
import           Eventful.Store.Sql                      (JSONString, SqlEvent, SqlEventStoreConfig,
                                                          jsonStringSerializer, sqlEventStoreReader,
                                                          sqlGlobalEventStoreReader)
import           Eventful.Store.Sqlite                   (sqliteEventStoreWriter)
import           Plutus.PAB.Monitoring.MonadLoggerBridge (MonadLoggerMsg, TraceLoggerT (..))
import           Plutus.PAB.Types                        (Source (..), toUUID)

newtype Connection =
    Connection (SqlEventStoreConfig SqlEvent JSONString, ConnectionPool)

data EventLogEffect event r where
    RefreshProjection
        :: GlobalStreamProjection state event
        -> EventLogEffect event (GlobalStreamProjection state event)
    RunCommand
        :: Aggregate state event command
        -> Source
        -> command
        -> EventLogEffect event [event]

makeEffect ''EventLogEffect

data EventLogBackend event =
    Sqlite Connection
    | InMemory (TVar (M.EventMap event))

handleEventLog ::
    forall effs event.
    ( Member (Reader (EventLogBackend event)) effs
    , LastMember IO effs
    , ToJSON event
    , FromJSON event
    ) =>
    Trace IO MonadLoggerMsg
    -> EventLogEffect event
    ~> Eff effs
handleEventLog trace m = do
    backend <- ask @(EventLogBackend event)
    case backend of
        Sqlite conn   -> handleEventLogSql trace conn m
        InMemory tvar -> handleEventLogTVar tvar m

-- | A handler for 'EventLogEffect' that uses an 'M.EventMap'
--   as the event store (in-memory)
handleEventLogTVar ::
    forall effs event.
    ( LastMember IO effs
    )
    => TVar (M.EventMap event)
    -> EventLogEffect event
    ~> Eff effs
handleEventLogTVar mp = \case
    RefreshProjection projection ->
        liftIO
            $ STM.atomically
            $ getLatestStreamProjection (M.tvarGlobalEventStoreReader mp) projection
    RunCommand aggregate source command ->
        liftIO
            $ STM.atomically
            $ commandStoredAggregate
                (M.tvarEventStoreWriter mp)
                (M.tvarEventStoreReader mp)
                aggregate
                (toUUID source)
                command

-- | A handler for 'EventLogEffect' that uses a SQL connection
--   as the event store (remote)
handleEventLogSql ::
       forall effs event.
       ( LastMember IO effs
       , ToJSON event
       , FromJSON event
       )
    => Trace IO MonadLoggerMsg
    -> Connection
    -> EventLogEffect event
    ~> Eff effs
handleEventLogSql trace connection = \case
    RefreshProjection projection -> do
        let Connection (sqlConfig, connectionPool) = connection
        sendM $ flip runTraceLoggerT trace $ do
            let reader =
                    serializedGlobalEventStoreReader jsonStringSerializer $
                    sqlGlobalEventStoreReader sqlConfig
            flip runSqlPool connectionPool $
                getLatestStreamProjection reader projection
    RunCommand aggregate source input -> do
        let Connection (sqlConfig, connectionPool) = connection
        sendM $ flip runTraceLoggerT trace $ do
            let reader :: VersionedEventStoreReader (SqlPersistT (TraceLoggerT IO)) event
                reader =
                    serializedVersionedEventStoreReader jsonStringSerializer $
                    sqlEventStoreReader sqlConfig
            let writer :: EventStoreWriter (SqlPersistT (TraceLoggerT IO)) event
                writer =
                    serializedEventStoreWriter jsonStringSerializer $
                    sqliteEventStoreWriter sqlConfig
            retryOnBusy . flip runSqlPool connectionPool $
                commandStoredAggregate
                    writer
                    reader
                    aggregate
                    (toUUID source)
                    input

runGlobalQuery ::
       Member (EventLogEffect event) effs
    => Projection a (VersionedStreamEvent event)
    -> Eff effs a
runGlobalQuery query =
    fmap streamProjectionState <$> refreshProjection $
    globalStreamProjection query
