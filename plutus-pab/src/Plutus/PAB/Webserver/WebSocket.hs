{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}

module Plutus.PAB.Webserver.WebSocket
    ( handleWS
    ) where

import qualified Cardano.BM.Configuration.Model          as CM
import           Cardano.BM.Trace                        (Trace)
import           Control.Concurrent.Async                (Async, async, waitAnyCancel)
import           Control.Exception                       (SomeException, handle)
import           Control.Monad                           (void, when)
import           Control.Monad.Freer                     (Eff, LastMember, Member)
import           Control.Monad.Freer.Delay               (DelayEffect, delayThread, handleDelayEffect)
import           Control.Monad.Freer.Extras.Log          (LogMsg, logInfo)
import           Control.Monad.Freer.Reader              (Reader, ask)
import           Control.Monad.Freer.WebSocket           (WebSocketEffect, acceptConnection, sendJSON)
import           Control.Monad.IO.Class                  (MonadIO, liftIO)
import           Data.Aeson                              (ToJSON)
import           Data.Time.Units                         (Second, TimeUnit)
import           Network.WebSockets.Connection           (Connection, PendingConnection, withPingThread)
import           Plutus.PAB.App                          (runApp)
import           Plutus.PAB.Core.ContractInstance.STM    (InstancesState)
import           Plutus.PAB.Effects.Contract             (ContractDefinitionStore, ContractEffect, ContractStore)
import           Plutus.PAB.Effects.Contract.ContractExe (ContractExe)
import qualified Plutus.PAB.Monitoring.PABLogMsg         as LM
import           Plutus.PAB.Types                        (Config, PABError)
import           Plutus.PAB.Webserver.Handler            (getChainReport, getContractReport)
import           Plutus.PAB.Webserver.Types              (StreamToClient (NewChainReport, NewContractReport),
                                                          WebSocketLogMsg (ClosedConnection, CreatedConnection))
import           Wallet.Effects                          (ChainIndexEffect)

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
chainReportThread = watchAndNotify (5 :: Second) getChainReport NewChainReport

contractStateThread ::
       ( Member WebSocketEffect effs
       , Member (ContractEffect ContractExe) effs
       , Member DelayEffect effs
       , Member (ContractDefinitionStore ContractExe) effs
       , Member (ContractStore ContractExe) effs
       )
    => Connection
    -> Eff effs ()
contractStateThread =
    watchAndNotify (3 :: Second) (getContractReport @ContractExe) NewContractReport

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

------------------------------------------------------------
-- Plumbing
------------------------------------------------------------
threadApp :: InstancesState -> Trace IO LM.PABLogMsg -> CM.Configuration -> Config -> Connection -> IO ()
threadApp instancesState trace logConfig config connection = do
    tasks :: [Async (Either PABError ())] <-
        traverse
            asyncApp
            [ chainReportThread connection
            , contractStateThread connection
            ]
    void $ waitAnyCancel tasks
  where
    asyncApp = async . runApp instancesState trace logConfig config . handleDelayEffect

handleClient :: InstancesState -> Trace IO LM.PABLogMsg -> CM.Configuration -> Config -> Connection -> IO ()
handleClient instancesState trace logConfig config connection =
    handle disconnect . withPingThread connection 30 (pure ()) $
    threadApp instancesState trace logConfig config connection
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
    => InstancesState
    -> Trace IO LM.PABLogMsg
    -> CM.Configuration
    -> PendingConnection
    -> Eff effs ()
handleWS instancesState trace logConfig pending = do
    (uuid, connection) <- acceptConnection pending
    config <- ask
    logInfo $ CreatedConnection uuid
    liftIO $ handleClient instancesState trace logConfig config connection
    logInfo $ ClosedConnection uuid
