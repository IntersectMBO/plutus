{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts   #-}
{-# LANGUAGE GADTs              #-}
{-# LANGUAGE NamedFieldPuns     #-}
{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE RankNTypes         #-}
{-# LANGUAGE TypeApplications   #-}
{-# LANGUAGE TypeOperators      #-}
{-

Servant handler for the Plutus PAB API
as a @PABAction t env@s.

-}
module Plutus.PAB.Core.Server(
    startServer,
    StatusStreamToClient(..),
    -- * Testing
    main
    ) where

import           Control.Applicative                               (Alternative (..))
import           Control.Concurrent                                (forkIO)
import qualified Control.Concurrent.STM                            as STM
import           Control.Exception                                 (SomeException, handle)
import           Control.Lens                                      (preview, (&))
import           Control.Monad                                     (guard, void)
import           Control.Monad.Except                              (ExceptT (ExceptT))
import           Control.Monad.IO.Class                            (liftIO)
import           Data.Aeson                                        (FromJSON, ToJSON)
import qualified Data.Aeson                                        as JSON
import           Data.Bifunctor                                    (Bifunctor (..))
import qualified Data.ByteString.Lazy.Char8                        as LBS
import qualified Data.Map                                          as Map
import           Data.Maybe                                        (mapMaybe)
import           Data.Proxy                                        (Proxy (..))
import           GHC.Generics                                      (Generic)
import           Language.Plutus.Contract.Effects.ExposeEndpoint   (ActiveEndpoint (..))
import           Language.PlutusTx.Coordination.Contracts.Currency (SimpleMPS (..))
import qualified Network.Wai.Handler.Warp                          as Warp
import qualified Network.WebSockets                                as WS
import           Network.WebSockets.Connection                     (Connection, PendingConnection, withPingThread)
import           Plutus.PAB.Core                                   (PABAction, PABRunner (..))
import qualified Plutus.PAB.Core                                   as Core
import           Plutus.PAB.Core.ContractInstance.STM              (OpenEndpoint (..))
import qualified Plutus.PAB.Effects.Contract                       as Contract
import           Plutus.PAB.Effects.Contract.ContractTest          (TestContracts (Currency))
import           Plutus.PAB.Events.Contract                        (ContractPABRequest, _UserEndpointRequest)
import           Plutus.PAB.Events.ContractInstanceState           (PartiallyDecodedResponse (hooks))
import           Plutus.PAB.Instances                              ()
import qualified Plutus.PAB.Simulator                              as Simulator
import           Plutus.PAB.Types                                  (PABError)
import           Plutus.PAB.Webserver.API                          (ContractActivationArgs (..),
                                                                    ContractInstanceClientState (..), NewAPI,
                                                                    WalletInfo (..))
import           Plutus.PAB.Webserver.Types                        (ContractSignatureResponse (..))
import           Servant                                           (Application, Handler, ServerT, (:<|>) ((:<|>)))
import qualified Servant                                           as Servant
import           Wallet.Emulator.Wallet                            (Wallet (..))
import           Wallet.Types                                      (ContractInstanceId)

handler ::
       forall t env.
       Contract.PABContract t =>
       (ContractActivationArgs (Contract.ContractDef t) -> PABAction t env ContractInstanceId)
            :<|> (ContractInstanceId -> PABAction t env (ContractInstanceClientState)
                                        :<|> (String -> JSON.Value -> PABAction t env ())
                                        :<|> (PendingConnection -> PABAction t env ()))
            :<|> PABAction t env [ContractInstanceClientState]
            :<|> PABAction t env [ContractSignatureResponse (Contract.ContractDef t)]
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

asHandler :: forall t env a. PABRunner t env -> PABAction t env a -> Handler a
asHandler PABRunner{runPABAction} = Servant.Handler . ExceptT . fmap (first mapError) . runPABAction where
    mapError :: PABError -> Servant.ServerError
    mapError e = Servant.err500 { Servant.errBody = LBS.pack $ show e }

app ::
    forall t env.
    ( FromJSON (Contract.ContractDef t)
    , ToJSON (Contract.ContractDef t)
    , Contract.PABContract t
    ) => PABRunner t env -> Application
app pabRunner = do
    let rest = Proxy @(NewAPI (Contract.ContractDef t))
        apiServer :: ServerT (NewAPI (Contract.ContractDef t)) Handler
        apiServer =
            Servant.hoistServer
                (Proxy @(NewAPI (Contract.ContractDef t)))
                (asHandler pabRunner)
                handler

    Servant.serve rest apiServer

-- | Start the server on the port. Returns an action that shuts it down again.
startServer ::
    forall t env.
    ( FromJSON (Contract.ContractDef t)
    , ToJSON (Contract.ContractDef t)
    , Contract.PABContract t
    ) => Warp.Port -> PABAction t env (PABAction t env ())
startServer port = do
    simRunner <- Core.pabRunner
    shutdownVar <- liftIO $ STM.atomically $ STM.newEmptyTMVar @()

    let shutdownHandler :: IO () -> IO ()
        shutdownHandler doShutdown = void $ forkIO $ do
            STM.atomically $ STM.takeTMVar shutdownVar
            putStrLn "webserver: shutting down"
            doShutdown
        warpSettings :: Warp.Settings
        warpSettings = Warp.defaultSettings
            & Warp.setPort port
            & Warp.setInstallShutdownHandler shutdownHandler
    _ <- liftIO $ forkIO $ Warp.runSettings warpSettings $ app simRunner
    pure (liftIO $ STM.atomically $ STM.putTMVar shutdownVar ())

-- HANDLERS

activateContract :: forall t env. Contract.PABContract t => ContractActivationArgs (Contract.ContractDef t) -> PABAction t env ContractInstanceId
activateContract ContractActivationArgs{caID, caWallet=WalletInfo{unWalletInfo=wallet}} = do
    Core.activateContract wallet caID

contractInstanceState :: forall t env. Contract.PABContract t => ContractInstanceId -> PABAction t env ContractInstanceClientState
contractInstanceState i = fromInternalState i . Contract.serialisableState (Proxy @t) <$> Contract.getState @t i

callEndpoint :: forall t env. ContractInstanceId -> String -> JSON.Value -> PABAction t env ()
callEndpoint a b = void . Core.callEndpointOnInstance a b

contractInstanceUpdates :: forall t env. ContractInstanceId -> PendingConnection -> PABAction t env ()
contractInstanceUpdates contractInstanceId pending = do
    Core.PABRunner{Core.runPABAction} <- Core.pabRunner
    liftIO $ do
        connection <- WS.acceptRequest pending
        handle disconnect . withPingThread connection 30 (pure ()) $ fmap (either (error . show) id) . runPABAction $ sendUpdatesToClient contractInstanceId connection
  where
    disconnect :: SomeException -> IO ()
    disconnect _ = pure ()

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
            update <- liftIO $ STM.atomically $ (NewObservableState <$> nextState currentState) <|> (NewActiveEndpoints <$> nextEndpoints currentEndpoints) <|> (ContractFinished <$> finalValue)
            liftIO $ WS.sendTextData connection $ JSON.encode update
            case update of
                NewObservableState newState -> go newState currentEndpoints
                NewActiveEndpoints eps      -> go currentState eps
                ContractFinished _          -> pure ()
    go initialState initialEndpoints

allInstanceStates :: forall t env. Contract.PABContract t => PABAction t env [ContractInstanceClientState]
allInstanceStates = do
    mp <- Contract.getActiveContracts @t
    let get i = fromInternalState i . Contract.serialisableState (Proxy @t) <$> Contract.getState @t i
    traverse get $ fst <$> Map.toList mp

availableContracts :: forall t env. Contract.PABContract t => PABAction t env [ContractSignatureResponse (Contract.ContractDef t)]
availableContracts = do
    def <- Contract.getDefinitions @t
    let mkSchema s = ContractSignatureResponse s <$> Contract.exportSchema @t s
    traverse mkSchema def

-- | Status updates for contract instances streamed to client
data StatusStreamToClient
    = NewObservableState JSON.Value -- ^ The observable state of the contract has changed.
    | NewActiveEndpoints [ActiveEndpoint] -- ^ The set of active endpoints has changed.
    | ContractFinished (Maybe JSON.Value) -- ^ Contract instance is done with an optional error message.
    deriving stock (Generic, Eq, Show)
    deriving anyclass (ToJSON, FromJSON)

-- | A little simulator test
main :: IO ()
main = void $ Simulator.runSimulation $ do
        instanceId <- Simulator.activateContract (Wallet 1) Currency
        shutdown <- startServer 8080
        _ <- liftIO getLine

        void $ do
            let endpointName = "Create native token"
                monetaryPolicy = SimpleMPS{tokenName="my token", amount = 10000}
            Simulator.callEndpointOnInstance instanceId endpointName monetaryPolicy
        _ <- liftIO getLine
        shutdown
