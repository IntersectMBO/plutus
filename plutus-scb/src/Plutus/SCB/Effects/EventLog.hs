{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs            #-}
{-# LANGUAGE LambdaCase       #-}
{-# LANGUAGE TemplateHaskell  #-}
{-# LANGUAGE TypeOperators    #-}

module Plutus.SCB.Effects.EventLog where

import           Control.Monad.Freer
import           Control.Monad.Freer.Extras (monadStateToState)
import           Control.Monad.Freer.Reader
import           Control.Monad.Freer.State  (State)
import           Control.Monad.Freer.TH     (makeEffect)
import qualified Control.Monad.IO.Unlift    as Unlift
import qualified Control.Monad.Logger       as MonadLogger
import           Data.Aeson                 (FromJSON, ToJSON)
import           Database.Persist.Sqlite
import           Eventful
import qualified Eventful.Store.Memory      as M
import           Eventful.Store.Sql
import           Eventful.Store.Sqlite      (sqliteEventStoreWriter)

import           Plutus.SCB.Query           (nullProjection)
import           Plutus.SCB.Types           (Source (..), toUUID)

newtype Connection =
    Connection (SqlEventStoreConfig SqlEvent JSONString, ConnectionPool)

data EventLogEffect event r where
    RefreshProjection :: GlobalStreamProjection state event
                     -> EventLogEffect event (GlobalStreamProjection state event)
    RunCommand :: Aggregate state event command -> Source -> command -> EventLogEffect event [event]
makeEffect ''EventLogEffect

-- | A handler for 'EventLogEffect' that uses an 'M.EventMap'
--   as the event store (in-memory)
handleEventLogState ::
    forall effs event.
    ( Member (State (M.EventMap event)) effs)
    => Eff (EventLogEffect event ': effs) ~> Eff effs
handleEventLogState = interpret $ \case
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
handleEventLogSql = interpret $ \case
    RefreshProjection projection -> do
        (Connection (sqlConfig, connectionPool)) <- ask
        sendM $ do
            let reader =
                    serializedGlobalEventStoreReader jsonStringSerializer $
                    sqlGlobalEventStoreReader sqlConfig
            flip runSqlPool connectionPool $
                getLatestStreamProjection reader projection
    RunCommand aggregate source input -> do
        (Connection (sqlConfig, connectionPool)) <- ask
        sendM $ do
            let reader =
                    serializedVersionedEventStoreReader jsonStringSerializer $
                    sqlEventStoreReader sqlConfig
            let writer =
                    addProcessBus
                        (serializedEventStoreWriter jsonStringSerializer $
                        sqliteEventStoreWriter sqlConfig)
                        reader
            retryOnBusy . flip runSqlPool connectionPool $
                commandStoredAggregate writer reader aggregate (toUUID source) input

runGlobalQuery ::
       Member (EventLogEffect event) effs
    => Projection a (VersionedStreamEvent event)
    -> Eff effs a
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
                  (ProcessManager nullProjection (const []) (const []))
                  subwriter
                  reader
                  ()
        ]
