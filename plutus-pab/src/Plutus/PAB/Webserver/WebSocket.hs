{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE NamedFieldPuns      #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}

module Plutus.PAB.Webserver.WebSocket
    ( combinedWebsocket
    , contractInstanceUpdates
    -- * Reports
    , getContractReport
    ) where

import           Control.Applicative                  (Alternative (..))
import qualified Control.Concurrent.STM               as STM
import           Control.Exception                    (SomeException, handle)
import           Control.Monad                        (guard)
import           Control.Monad.IO.Class               (liftIO)
import qualified Data.Aeson                           as JSON
import           Data.Map                             as Map
import           Data.Proxy                           (Proxy (..))
import qualified Network.WebSockets                   as WS
import           Network.WebSockets.Connection        (Connection, PendingConnection)
import           Plutus.PAB.Core                      (PABAction)
import qualified Plutus.PAB.Core                      as Core
import           Plutus.PAB.Core.ContractInstance.STM (OpenEndpoint (..))
import qualified Plutus.PAB.Effects.Contract          as Contract
import           Plutus.PAB.Webserver.API             (StatusStreamToClient (..))
import           Plutus.PAB.Webserver.Types           (ContractReport (..), ContractSignatureResponse (..))
import           Wallet.Types                         (ContractInstanceId (..))

------------------------------------------------------------
-- Message processors.
------------------------------------------------------------

-- contractStateThread ::
--        ( Member WebSocketEffect effs
--        , Member (ContractEffect ContractExe) effs
--        , Member DelayEffect effs
--        , Member (ContractDefinitionStore ContractExe) effs
--        , Member (ContractStore ContractExe) effs
--        )
--     => Connection
--     -> Eff effs ()
-- contractStateThread _ = pure () -- FIXME
--     -- watchAndNotify (3 :: Second) (getContractReport @ContractExe) NewContractReport

-- watchAndNotify ::
--        ( TimeUnit t
--        , Member DelayEffect effs
--        , Member WebSocketEffect effs
--        , Eq a
--        , ToJSON b
--        )
--     => t
--     -> Eff effs a
--     -> (a -> b)
--     -> Connection
--     -> Eff effs ()
-- watchAndNotify time query wrapper connection = pure () -- FIXME
--     -- watchForChanges time query (sendJSON connection . wrapper)

combinedWebsocket :: forall t env. PendingConnection -> PABAction t env ()
combinedWebsocket _ = do
    -- Core.PABRunner{Core.runPABAction} <- Core.pabRunner
    -- Subscribe / unsubscribe to updates
    -- slot updates
    pure ()

contractInstanceUpdates :: forall t env. ContractInstanceId -> PendingConnection -> PABAction t env ()
contractInstanceUpdates contractInstanceId pending = do
    Core.PABRunner{Core.runPABAction} <- Core.pabRunner
    liftIO $ do
        connection <- WS.acceptRequest pending
        handle disconnect . WS.withPingThread connection 30 (pure ()) $ fmap (either (error . show) id) . runPABAction $ sendUpdatesToClient contractInstanceId connection
  where
    disconnect :: SomeException -> IO ()
    disconnect _ = pure ()

getContractReport :: forall t env. Contract.PABContract t => PABAction t env (ContractReport (Contract.ContractDef t))
getContractReport = do
    installedContracts <- Contract.getDefinitions @t
    activeContractIDs <- fmap fst . Map.toList <$> Contract.getActiveContracts @t
    crAvailableContracts <-
        traverse
            (\t -> ContractSignatureResponse t <$> Contract.exportSchema @t t)
            installedContracts
    crActiveContractStates <- traverse (\i -> Contract.getState @t i >>= \s -> pure (i, Contract.serialisableState (Proxy @t) s)) activeContractIDs
    pure ContractReport {crAvailableContracts, crActiveContractStates}

sendUpdatesToClient :: forall t env. ContractInstanceId -> Connection -> PABAction t env ()
sendUpdatesToClient instanceId connection = do
    (getState, getEndpoints, finalValue) <- (,,) <$> Core.observableState instanceId <*> fmap (fmap (fmap oepName)) (Core.activeEndpoints instanceId) <*> Core.finalResult instanceId
    (initialState, initialEndpoints) <- liftIO $ STM.atomically $ (,) <$> getState <*> getEndpoints
    let nextState oldState = do
            newState <- getState
            guard $ newState /= oldState
            pure newState

        nextEndpoints oldEndpoints = do
            newEndpoints <- getEndpoints
            guard $ newEndpoints /= oldEndpoints
            pure newEndpoints

        go currentState currentEndpoints = do
            update' <- liftIO $ STM.atomically $ (NewObservableState <$> nextState currentState) <|> (NewActiveEndpoints <$> nextEndpoints currentEndpoints) <|> (ContractFinished <$> finalValue)
            liftIO $ WS.sendTextData connection $ JSON.encode update'
            case update' of
                NewObservableState newState -> go newState currentEndpoints
                NewActiveEndpoints eps      -> go currentState eps
                ContractFinished _          -> pure ()
    go initialState initialEndpoints
