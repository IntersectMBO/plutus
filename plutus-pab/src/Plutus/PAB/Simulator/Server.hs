{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts   #-}
{-# LANGUAGE GADTs              #-}
{-# LANGUAGE NamedFieldPuns     #-}
{-# LANGUAGE RankNTypes         #-}
{-# LANGUAGE TypeApplications   #-}
{-# LANGUAGE TypeOperators      #-}
{-

Experimental webserver implementing the new PAB API.

-}
module Plutus.PAB.Simulator.Server(
    startServer,
    StatusStreamToClient(..)
    ) where

import           Control.Applicative                             (Alternative (..))
import qualified Control.Concurrent.STM                          as STM
import           Control.Exception                               (SomeException, handle)
import           Control.Lens                                    (preview)
import           Control.Monad                                   (guard, void)
import           Control.Monad.IO.Class                          (liftIO)
import           Data.Aeson                                      (FromJSON, ToJSON)
import qualified Data.Aeson                                      as JSON
import qualified Data.Map                                        as Map
import           Data.Maybe                                      (mapMaybe)
import           Data.Proxy                                      (Proxy (..))
import           GHC.Generics                                    (Generic)
import           Language.Plutus.Contract.Effects.ExposeEndpoint (ActiveEndpoint (..))
import           Language.Plutus.Contract.Resumable              (Request (..))
import qualified Network.WebSockets                              as WS
import           Network.WebSockets.Connection                   (Connection, PendingConnection, receiveData,
                                                                  withPingThread)
import           Plutus.PAB.Core.ContractInstance.STM            (OpenEndpoint (..))
import           Plutus.PAB.Effects.Contract                     (PABContract (..))
import qualified Plutus.PAB.Effects.Contract                     as Contract
import           Plutus.PAB.Effects.Contract.ContractTest        (TestContracts (AtomicSwap, Currency))
import           Plutus.PAB.Events.Contract                      (ContractPABRequest, _UserEndpointRequest)
import           Plutus.PAB.Events.ContractInstanceState         (PartiallyDecodedResponse (hooks))
import           Plutus.PAB.Simulator                            (SimRunner (..), Simulation)
import qualified Plutus.PAB.Simulator                            as Simulator
import           Plutus.PAB.Webserver.API                        (ContractActivationArgs (..),
                                                                  ContractInstanceClientState (..), NewAPI,
                                                                  WalletInfo (..))
import           Plutus.PAB.Webserver.Types                      (ContractSignatureResponse (..))
import           Servant                                         (Application, Handler, ServerT, (:<|>) ((:<|>)))
import qualified Servant                                         as Servant
import           Wallet.Emulator.Wallet                          (Wallet (..))
import           Wallet.Types                                    (ContractInstanceId)

handler ::
       (ContractActivationArgs TestContracts -> Simulation ContractInstanceId)
            :<|> (ContractInstanceId -> Simulation (ContractInstanceClientState)
                                        :<|> (String -> JSON.Value -> Simulation ())
                                        :<|> (PendingConnection -> Simulation ()))
            :<|> Simulation [ContractInstanceClientState]
            :<|> Simulation [ContractSignatureResponse TestContracts]
handler =
        (activateContract
            :<|> (\x -> contractInstanceState x :<|> callEndpoint x :<|> contractInstanceUpdates x)
            :<|> allInstanceStates
            :<|> availableContracts)

fromInternalState ::
    ContractInstanceId
    -> PartiallyDecodedResponse ContractPABRequest
    -> ContractInstanceClientState
fromInternalState i resp =
    ContractInstanceClientState
        { cicContract = i
        , cicCurrentState =
            let hks' = mapMaybe (traverse (preview _UserEndpointRequest)) (hooks resp)
            in resp { hooks = hks' }
        }

asHandler :: SimRunner -> Simulation a -> Handler a
asHandler = undefined

app :: SimRunner -> Application
app simRunner = do
    let rest = Proxy @(NewAPI TestContracts)
        apiServer :: ServerT (NewAPI TestContracts) Handler
        apiServer =
            Servant.hoistServer
                (Proxy @(NewAPI TestContracts))
                (asHandler simRunner)
                handler

    Servant.serve rest _

-- | Start the server. Returns an action that shuts it down again.
startServer :: Simulation (Simulation ())
startServer = do

    pure $ pure ()

-- HANDLERS

activateContract ::
    ContractActivationArgs TestContracts
    -> Simulation ContractInstanceId
activateContract ContractActivationArgs{caID, caWallet=WalletInfo{unWalletInfo=wallet}} = do
    Simulator.agentAction wallet $ Simulator.activateContract caID

contractInstanceState :: ContractInstanceId -> Simulation ContractInstanceClientState
contractInstanceState i = fromInternalState i <$> Contract.getState @TestContracts i

callEndpoint :: ContractInstanceId -> String -> JSON.Value -> Simulation ()
callEndpoint a b = void . Simulator.callEndpointOnInstance a b

contractInstanceUpdates :: ContractInstanceId -> PendingConnection -> Simulation ()
contractInstanceUpdates contractInstanceId pending = do
    Simulator.SimRunner{Simulator.runSim} <- Simulator.mkRunSim
    liftIO $ do
        connection <- WS.acceptRequest pending
        handle disconnect . withPingThread connection 30 (pure ()) $ fmap (either (error . show) id) . runSim $ sendUpdatesToClient contractInstanceId connection
  where
    disconnect :: SomeException -> IO ()
    disconnect _ = pure ()

sendUpdatesToClient :: ContractInstanceId -> Connection -> Simulation ()
sendUpdatesToClient instanceId connection = do
    (getState, getEndpoints, finalValue) <- (,,) <$> Simulator.observableState instanceId <*> fmap (fmap (fmap oepName)) (Simulator.activeEndpoints instanceId) <*> Simulator.finalResult instanceId
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
            update <- liftIO $ STM.atomically $ (NewObservableState <$> nextState currentState) <|> (NewActiveEndpoints <$> nextEndpoints currentEndpoints) <|> (ContractFinished <$> finalValue)
            liftIO $ WS.sendTextData connection $ JSON.encode update
            case update of
                NewObservableState newState -> go newState currentEndpoints
                NewActiveEndpoints eps      -> go currentState eps
                ContractFinished _          -> pure ()
    go initialState initialEndpoints

allInstanceStates :: Simulation [ContractInstanceClientState]
allInstanceStates = do
    mp <- Contract.getActiveContracts @TestContracts
    let get i = fromInternalState i <$> Contract.getState @TestContracts i
    traverse get $ fst <$> Map.toList mp

availableContracts :: Simulation [ContractSignatureResponse TestContracts]
availableContracts =
    let mkSchema s = ContractSignatureResponse s <$> Contract.exportSchema @TestContracts s
    in traverse mkSchema [Currency, AtomicSwap]

-- | Status updates for contract instances streamed to client
data StatusStreamToClient
    = NewObservableState JSON.Value -- ^ The observable state of the contract has changed.
    | NewActiveEndpoints [ActiveEndpoint] -- ^ The set of active endpoints has changed.
    | ContractFinished (Maybe JSON.Value) -- ^ Contract instance is done with an optional error message.
    deriving stock (Generic, Eq, Show)
    deriving anyclass (ToJSON, FromJSON)
