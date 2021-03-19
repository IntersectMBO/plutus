{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE NamedFieldPuns      #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-

Handlers for the websockets exposed by the PAB.

-}
module Plutus.PAB.Webserver.WebSocket
    ( combinedWebsocket
    , contractInstanceUpdates
    -- * Reports
    , getContractReport
    ) where

import           Control.Applicative                  (Alternative (..))
import           Control.Concurrent.STM               (STM)
import qualified Control.Concurrent.STM               as STM
import           Control.Exception                    (SomeException, handle)
import           Control.Monad                        (guard)
import           Control.Monad.IO.Class               (liftIO)
import           Data.Aeson                           (ToJSON)
import qualified Data.Aeson                           as JSON
import           Data.Map                             as Map
import           Data.Proxy                           (Proxy (..))
import           Data.Set                             (Set)
import qualified Data.Set                             as Set
import qualified Network.WebSockets                   as WS
import           Network.WebSockets.Connection        (Connection, PendingConnection)
import           Plutus.PAB.Core                      (PABAction)
import qualified Plutus.PAB.Core                      as Core
import           Plutus.PAB.Core.ContractInstance.STM (OpenEndpoint (..))
import qualified Plutus.PAB.Effects.Contract          as Contract
import           Plutus.PAB.Webserver.API             (CombinedWSStreamToClient (..), InstanceStatusToClient (..))
import           Plutus.PAB.Webserver.Types           (ContractReport (..), ContractSignatureResponse (..))
import           Wallet.Emulator.Wallet               (Wallet)
import           Wallet.Types                         (ContractInstanceId (..))


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

-- | An STM stream of 'a's
data STMStream a =
    STMStream
        { iuUpdate :: a
        , iuNext   :: Maybe (STM (STMStream a))
        }
        deriving Functor

type CombinedUpdate = STMStream CombinedWSStreamToClient

combinedUpdates :: forall t env. PABAction t env (STM CombinedUpdate)
combinedUpdates = do
    getSlot <- Core.currentSlot
    initialSlot <- liftIO $ STM.atomically getSlot
    let nextSlot currentSlot = do
            s <- getSlot
            guard (s > currentSlot)
            pure s

        go currentSlot = do
            update' <- SlotChange <$> nextSlot currentSlot
            let next = case update' of
                    SlotChange c' -> Just (go c')
                    _             -> Nothing -- FIXME
            pure STMStream{iuUpdate=update', iuNext=next}
    pure $ go initialSlot

-- | The subscriptions for a websocket (wallet funds and contract instance notifications)
data WSState = WSState
    { wsInstances :: STM.TVar (Set ContractInstanceId) -- ^ Contract instances that we want updates for
    , wsWallets   :: STM.TVar (Set Wallet) -- ^ Wallets whose funds we are watching
    }

initialWSState :: STM WSState
initialWSState = WSState <$> STM.newTVar mempty <*> STM.newTVar mempty


-- | An STM stream of 'InstanceStatusToClient' updates
type InstanceUpdate = STMStream InstanceStatusToClient

-- | Get a stream of instance updates for a given instance ID
instanceUpdates :: forall t env. ContractInstanceId -> PABAction t env (STM InstanceUpdate)
instanceUpdates instanceId = do
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
            update' <- (NewObservableState <$> nextState currentState) <|> (NewActiveEndpoints <$> nextEndpoints currentEndpoints) <|> (ContractFinished <$> finalValue)
            let next = case update' of
                        NewObservableState newState -> Just $ go newState currentEndpoints
                        NewActiveEndpoints eps      -> Just $ go currentState eps
                        ContractFinished _          -> Nothing
            pure STMStream{iuUpdate = update', iuNext = next}
    pure $ go initialState initialEndpoints

-- | Send all updates from an 'STMStream' to a websocket until it finishes.
streamToWebsocket :: forall t env a. ToJSON a => Connection -> STMStream a -> PABAction t env ()
streamToWebsocket connection stream = do
    let go STMStream{iuUpdate, iuNext} = do
            liftIO $ WS.sendTextData connection $ JSON.encode iuUpdate
            case iuNext of
                Nothing -> pure ()
                Just n  -> liftIO (STM.atomically n) >>= go
    go stream

sendContractInstanceUpdatesToClient :: forall t env. ContractInstanceId -> Connection -> PABAction t env ()
sendContractInstanceUpdatesToClient instanceId connection = instanceUpdates instanceId >>= liftIO . STM.atomically >>= streamToWebsocket connection

contractInstanceUpdates :: forall t env. ContractInstanceId -> PendingConnection -> PABAction t env ()
contractInstanceUpdates contractInstanceId pending = do
    Core.PABRunner{Core.runPABAction} <- Core.pabRunner
    liftIO $ do
        connection <- WS.acceptRequest pending
        handle disconnect . WS.withPingThread connection 30 (pure ()) $ fmap (either (error . show) id) . runPABAction $ sendContractInstanceUpdatesToClient contractInstanceId connection
  where
    disconnect :: SomeException -> IO ()
    disconnect _ = pure ()

combinedWebsocket :: forall t env. PendingConnection -> PABAction t env ()
combinedWebsocket pending = do
    Core.PABRunner{Core.runPABAction} <- Core.pabRunner
    liftIO $ do
        connection <- WS.acceptRequest pending
        handle disconnect . WS.withPingThread connection 30 (pure ()) $ fmap (either (error . show) id) . runPABAction $ sendCombinedUpdatesToClient connection
  where
    disconnect :: SomeException -> IO ()
    disconnect _ = pure ()

sendCombinedUpdatesToClient :: forall t env. Connection -> PABAction t env ()
sendCombinedUpdatesToClient connection = combinedUpdates >>= liftIO . STM.atomically >>= streamToWebsocket connection

