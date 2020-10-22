{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators       #-}

module Plutus.SCB.Webserver.WebSocket
    ( handleWS
    ) where

import qualified Cardano.BM.Configuration.Model as CM
import           Cardano.BM.Trace               (Trace)
import           Cardano.Metadata.Types         (MetadataEffect)
import qualified Cardano.Metadata.Types         as Metadata
import           Control.Concurrent.Async       (Async, async, waitAnyCancel)
import           Control.Exception              (SomeException, handle)
import           Control.Monad                  (forever, void, when)
import           Control.Monad.Freer            (Eff, LastMember, Member)
import           Control.Monad.Freer.Delay      (DelayEffect, delayThread, handleDelayEffect)
import           Control.Monad.Freer.Extra.Log  (LogMsg, logDebug, logInfo)
import           Control.Monad.Freer.Reader     (Reader, ask)
import           Control.Monad.Freer.WebSocket  (WebSocketEffect, acceptConnection, receiveJSON, sendJSON)
import           Control.Monad.IO.Class         (MonadIO, liftIO)
import           Data.Aeson                     (ToJSON)
import           Data.Time.Units                (Second, TimeUnit)
import           Network.WebSockets.Connection  (Connection, PendingConnection, withPingThread)
import           Plutus.SCB.App                 (runApp)
import           Plutus.SCB.Effects.Contract    (ContractEffect)
import           Plutus.SCB.Effects.EventLog    (EventLogEffect)
import           Plutus.SCB.Events              (ChainEvent)
import           Plutus.SCB.SCBLogMsg           (SCBLogMsg)
import           Plutus.SCB.Types               (Config, ContractExe, SCBError)
import           Plutus.SCB.Webserver.Handler   (getChainReport, getContractReport, getEvents)
import           Plutus.SCB.Webserver.Types     (StreamToClient (ErrorResponse, FetchedProperties, FetchedProperty, NewChainEvents, NewChainReport, NewContractReport),
                                                 StreamToServer (FetchProperties, FetchProperty),
                                                 WebSocketLogMsg (ClosedConnection, CreatedConnection, ReceivedWebSocketRequest, SendingWebSocketResponse))
import           Wallet.Effects                 (ChainIndexEffect)

------------------------------------------------------------
-- Message processors.
------------------------------------------------------------
chainReportThread ::
       ( Member ChainIndexEffect effs
       , Member MetadataEffect effs
       , Member DelayEffect effs
       , Member WebSocketEffect effs
       )
    => Connection
    -> Eff effs ()
chainReportThread = watchAndNotify (5 :: Second) getChainReport NewChainReport

contractStateThread ::
       ( Member WebSocketEffect effs
       , Member (EventLogEffect (ChainEvent ContractExe)) effs
       , Member (ContractEffect ContractExe) effs
       , Member DelayEffect effs
       )
    => Connection
    -> Eff effs ()
contractStateThread =
    watchAndNotify (3 :: Second) getContractReport NewContractReport

eventsThread ::
       ( Member WebSocketEffect effs
       , Member (EventLogEffect (ChainEvent ContractExe)) effs
       , Member DelayEffect effs
       )
    => Connection
    -> Eff effs ()
eventsThread =
    watchAndNotify (15 :: Second) getEvents NewChainEvents

watchAndNotify ::
       ( TimeUnit t
       , Member DelayEffect effs
       , Member WebSocketEffect effs
       , Eq a
       , ToJSON b
       )
    => t
    -> Eff effs a
    -> (a -> b)
    -> Connection
    -> Eff effs ()
watchAndNotify time query wrapper connection =
    watchForChanges time query (sendJSON connection . wrapper)

-- TODO Polling is icky. But we can't use Eventful's hook system
-- because that relies all events coming in from the same thread. We
-- can't guarantee that. (eg. We could be running on the server, but
-- the update came via the CLI.)
--
-- Can we use the DB commit hook instead?
-- https://www.sqlite.org/c3ref/commit_hook.html
watchForChanges ::
       (TimeUnit t, Eq a, Member DelayEffect effs)
    => t
    -> Eff effs a
    -> (a -> Eff effs ())
    -> Eff effs ()
watchForChanges time query notify = go Nothing
  where
    go oldValue = do
        newValue <- query
        when (oldValue /= Just newValue) (notify newValue)
        delayThread time
        go $ Just newValue

queryHandlerThread ::
       forall effs.
       ( Member WebSocketEffect effs
       , Member MetadataEffect effs
       , Member (LogMsg WebSocketLogMsg) effs
       )
    => Connection
    -> Eff effs ()
queryHandlerThread connection =
    forever $ do
        rawRequest <- receiveJSON connection
        logDebug $ ReceivedWebSocketRequest rawRequest
        response <-
            case rawRequest of
                Left err      -> pure $ ErrorResponse err
                Right request -> handler request
        logDebug $ SendingWebSocketResponse response
        sendJSON connection response
  where
    handler :: StreamToServer -> Eff effs StreamToClient
    handler (FetchProperties subject) =
        FetchedProperties <$> Metadata.getProperties subject
    handler (FetchProperty subject propertyKey) =
        FetchedProperty subject <$> Metadata.getProperty subject propertyKey

------------------------------------------------------------
-- Plumbing
------------------------------------------------------------
threadApp :: Trace IO SCBLogMsg -> CM.Configuration -> Config -> Connection -> IO ()
threadApp trace logConfig config connection = do
    tasks :: [Async (Either SCBError ())] <-
        traverse
            asyncApp
            [ chainReportThread connection
            , contractStateThread connection
            , eventsThread connection
            , queryHandlerThread connection
            ]
    void $ waitAnyCancel tasks
  where
    asyncApp = async . runApp trace logConfig config . handleDelayEffect

handleClient :: Trace IO SCBLogMsg -> CM.Configuration -> Config -> Connection -> IO ()
handleClient trace logConfig config connection =
    handle disconnect . withPingThread connection 30 (pure ()) $
    threadApp trace logConfig config connection
  where
    disconnect :: SomeException -> IO ()
    disconnect _ = pure ()

handleWS ::
       ( LastMember m effs
       , MonadIO m
       , Member (LogMsg WebSocketLogMsg) effs
       , Member (Reader Config) effs
       , Member WebSocketEffect effs
       )
    => Trace IO SCBLogMsg
    -> CM.Configuration
    -> PendingConnection
    -> Eff effs ()
handleWS trace logConfig pending = do
    (uuid, connection) <- acceptConnection pending
    config <- ask
    logInfo $ CreatedConnection uuid
    liftIO $ handleClient trace logConfig config connection
    logInfo $ ClosedConnection uuid
