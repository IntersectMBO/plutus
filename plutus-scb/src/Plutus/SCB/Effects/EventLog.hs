{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs            #-}
{-# LANGUAGE LambdaCase       #-}
{-# LANGUAGE TemplateHaskell  #-}
{-# LANGUAGE TypeOperators    #-}

module Plutus.SCB.Effects.EventLog where

import           Control.Monad.Freer        (Eff, LastMember, Member, interpret, sendM, type (~>))
import           Control.Monad.Freer.Extras (monadStateToState)
import           Control.Monad.Freer.Reader (Reader, ask)
import           Control.Monad.Freer.State  (State)
import           Control.Monad.Freer.TH     (makeEffect)
import qualified Control.Monad.IO.Unlift    as Unlift
import qualified Control.Monad.Logger       as MonadLogger
import           Data.Aeson                 (FromJSON, ToJSON)
import           Database.Persist.Sqlite    (ConnectionPool, SqlPersistT, retryOnBusy, runSqlPool)
import           Eventful                   (Aggregate, EventStoreWriter, GlobalStreamProjection, Projection,
                                             VersionedEventStoreReader, VersionedStreamEvent, commandStoredAggregate,
                                             getLatestStreamProjection, globalStreamProjection,
                                             serializedEventStoreWriter, serializedGlobalEventStoreReader,
                                             serializedVersionedEventStoreReader, streamProjectionState)
import qualified Eventful.Store.Memory      as M
import           Eventful.Store.Sql         (JSONString, SqlEvent, SqlEventStoreConfig, jsonStringSerializer,
                                             sqlEventStoreReader, sqlGlobalEventStoreReader)
import           Eventful.Store.Sqlite      (sqliteEventStoreWriter)
import           Plutus.SCB.Types           (Source (..), toUUID)

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

-- | A handler for 'EventLogEffect' that uses an 'M.EventMap'
--   as the event store (in-memory)
handleEventLogState ::
       forall effs event. (Member (State (M.EventMap event)) effs)
    => Eff (EventLogEffect event ': effs) ~> Eff effs
handleEventLogState =
    interpret $ \case
        RefreshProjection projection ->
            monadStateToState $
            getLatestStreamProjection M.stateGlobalEventStoreReader projection
        RunCommand aggregate source command ->
            monadStateToState $
            commandStoredAggregate
                M.stateEventStoreWriter
                M.stateEventStoreReader
                aggregate
                (toUUID source)
                command

-- | A handler for 'EventLogEffect' that uses a SQL connection
--   as the event store (remote)
handleEventLogSql ::
       forall effs event m.
       ( Member (Reader Connection) effs
       , LastMember m effs
       , ToJSON event
       , FromJSON event
       , MonadLogger.MonadLogger m
       , Unlift.MonadUnliftIO m
       )
    => Eff (EventLogEffect event ': effs) ~> Eff effs
handleEventLogSql =
    interpret $ \case
        RefreshProjection projection -> do
            (Connection (sqlConfig, connectionPool)) <- ask
            sendM $ do
                let reader =
                        serializedGlobalEventStoreReader jsonStringSerializer $
                        sqlGlobalEventStoreReader sqlConfig
                flip runSqlPool connectionPool $
                    getLatestStreamProjection reader projection
        RunCommand aggregate source input -> do
            Connection (sqlConfig, connectionPool) <- ask
            sendM $ do
                let reader :: VersionedEventStoreReader (SqlPersistT m) event
                    reader =
                        serializedVersionedEventStoreReader jsonStringSerializer $
                        sqlEventStoreReader sqlConfig
                let writer :: EventStoreWriter (SqlPersistT m) event
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
