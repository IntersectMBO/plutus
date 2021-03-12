{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs            #-}
{-# LANGUAGE NamedFieldPuns   #-}
{-# LANGUAGE RankNTypes       #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators    #-}
{-

Experimental webserver implementing the new PAB API.

-}
module Plutus.PAB.Simulator.Server(startServer) where

import           Control.Exception                        (SomeException, handle)
import           Control.Lens                             (preview)
import           Control.Monad                            (void)
import           Control.Monad.IO.Class                   (liftIO)
import qualified Data.Aeson                               as JSON
import qualified Data.Map                                 as Map
import           Data.Maybe                               (mapMaybe)
import qualified Network.WebSockets                       as WS
import           Network.WebSockets.Connection            (Connection, PendingConnection, receiveData, withPingThread)
import           Plutus.PAB.Effects.Contract              (PABContract (..))
import qualified Plutus.PAB.Effects.Contract              as Contract
import           Plutus.PAB.Effects.Contract.ContractTest (TestContracts (AtomicSwap, Currency))
import           Plutus.PAB.Events.Contract               (ContractPABRequest, _UserEndpointRequest)
import           Plutus.PAB.Events.ContractInstanceState  (PartiallyDecodedResponse (hooks))
import           Plutus.PAB.Simulator                     (Simulation)
import qualified Plutus.PAB.Simulator                     as Simulator
import           Plutus.PAB.Webserver.API                 (ContractActivationArgs (..),
                                                           ContractInstanceClientState (..), WalletInfo (..))
import           Plutus.PAB.Webserver.Types               (ContractSignatureResponse (..))
import           Servant                                  ((:<|>) ((:<|>)))
import           Wallet.Emulator.Wallet                   (Wallet (..))
import           Wallet.Types                             (ContractInstanceId)

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

-- | Start the server. Returns an action that shuts it down again.
startServer :: Simulation (Simulation ())
startServer = pure $ pure ()

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
        handle disconnect . withPingThread connection 30 (pure ()) $ fmap (either (error . show) id) . runSim $ sendUpdatesToClient connection
  where
    disconnect :: SomeException -> IO ()
    disconnect _ = pure ()

sendUpdatesToClient :: Connection -> Simulation ()
sendUpdatesToClient = undefined

allInstanceStates :: Simulation [ContractInstanceClientState]
allInstanceStates = do
    mp <- Contract.getActiveContracts @TestContracts
    let get i = fromInternalState i <$> Contract.getState @TestContracts i
    traverse get $ fst <$> Map.toList mp

availableContracts :: Simulation [ContractSignatureResponse TestContracts]
availableContracts =
    let mkSchema s = ContractSignatureResponse s <$> Contract.exportSchema @TestContracts s
    in traverse mkSchema [Currency, AtomicSwap]
