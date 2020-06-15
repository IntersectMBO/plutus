{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}

module Plutus.SCB.Webserver.WebSocket
    ( handleWS
    ) where

import           Control.Concurrent.Async      (Async, async, waitAnyCancel)
import           Control.Exception             (SomeException, handle)
import           Control.Monad                 (forever, void, when)
import           Control.Monad.Freer           (Eff, LastMember, Member)
import           Control.Monad.Freer.Delay     (DelayEffect, delayThread, handleDelayEffect)
import           Control.Monad.Freer.Extra.Log (LogMsg, logInfo)
import           Control.Monad.Freer.Reader    (Reader, ask)
import           Control.Monad.Freer.WebSocket (WebSocketEffect, acceptConnection, receiveJSON, sendJSON)
import           Control.Monad.IO.Class        (MonadIO, liftIO)
import           Control.Monad.Logger          (LogLevel (LevelDebug))
import qualified Data.Text                     as Text
import           Data.Time.Units               (Second, TimeUnit)
import           Network.WebSockets.Connection (Connection, PendingConnection, withPingThread)
import           Plutus.SCB.App                (runApp)
import           Plutus.SCB.Effects.Contract   (ContractEffect)
import           Plutus.SCB.Effects.EventLog   (EventLogEffect)
import           Plutus.SCB.Events             (ChainEvent)
import           Plutus.SCB.Types              (Config, ContractExe, SCBError)
import           Plutus.SCB.Webserver.Handler  (getChainReport, getContractReport)
import           Plutus.SCB.Webserver.Types    (StreamToClient (Echo, ErrorResponse, NewChainReport, NewContractReport),
                                                StreamToServer (Ping),
                                                WebSocketLogMsg (ClosedConnection, CreatedConnection))
import           Wallet.Effects                (ChainIndexEffect)

timeBetweenChainReports :: Second
timeBetweenChainReports = 10

timeBetweenEvents :: Second
timeBetweenEvents = 3

------------------------------------------------------------
-- Message processors.
------------------------------------------------------------
chainReportThread ::
       ( Member ChainIndexEffect effs
       , Member DelayEffect effs
       , Member WebSocketEffect effs
       )
    => Connection
    -> Eff effs ()
chainReportThread connection =
    pollAndNotifyOnChange timeBetweenChainReports getChainReport notify
  where
    notify newReport =
        sendJSON connection $ NewChainReport @ContractExe newReport

contractStateThread ::
       ( Member WebSocketEffect effs
       , Member (EventLogEffect (ChainEvent ContractExe)) effs
       , Member (ContractEffect ContractExe) effs
       , Member DelayEffect effs
       )
    => Connection
    -> Eff effs ()
contractStateThread connection =
    pollAndNotifyOnChange timeBetweenEvents getContractReport notify
  where
    notify newReport =
        sendJSON connection $ NewContractReport @ContractExe newReport

chatThread :: Member WebSocketEffect effs => Connection -> Eff effs ()
chatThread connection =
    forever $ do
        payload :: Either String (StreamToServer ContractExe) <-
            receiveJSON connection
        sendJSON connection $ handleStreamingMessage payload

-- TODO Polling is icky. But we can't use Eventful's hook system
-- because that relies all events coming in from the same thread. We
-- can't guarantee that. (eg. We could be running on the server, but
-- the update came via the CLI.)
--
-- Can we use the DB commit hook instead?
-- https://www.sqlite.org/c3ref/commit_hook.html
pollAndNotifyOnChange ::
       (TimeUnit t, Eq a, Member DelayEffect effs)
    => t
    -> Eff effs a
    -> (a -> Eff effs ())
    -> Eff effs ()
pollAndNotifyOnChange time query notify = go Nothing
  where
    go oldValue = do
        newValue <- query
        when (oldValue /= Just newValue) (notify newValue)
        delayThread time
        go $ Just newValue

handleStreamingMessage :: Either String (StreamToServer t) -> StreamToClient t
handleStreamingMessage (Left err)         = ErrorResponse $ Text.pack err
handleStreamingMessage (Right (Ping msg)) = Echo msg

------------------------------------------------------------
-- Plumbing
------------------------------------------------------------
threadApp :: Config -> Connection -> IO ()
threadApp config connection = do
    tasks :: [Async (Either SCBError ())] <-
        traverse
            asyncApp
            [ chainReportThread connection
            , contractStateThread connection
            , chatThread connection
            ]
    void $ waitAnyCancel tasks
  where
    asyncApp = async . runApp LevelDebug config . handleDelayEffect

handleClient :: Config -> Connection -> IO ()
handleClient config connection =
    handle disconnect . withPingThread connection 30 (pure ()) $
    threadApp config connection
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
    => PendingConnection
    -> Eff effs ()
handleWS pending = do
    (uuid, connection) <- acceptConnection pending
    config <- ask
    logInfo $ CreatedConnection uuid
    liftIO $ handleClient config connection
    logInfo $ ClosedConnection uuid
