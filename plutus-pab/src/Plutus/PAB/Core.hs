{-# LANGUAGE AllowAmbiguousTypes   #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE DeriveGeneric         #-}
{-# LANGUAGE DerivingStrategies    #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns        #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}

module Plutus.PAB.Core
    ( PABEffects
    , PABAction
    , EffectHandlers(..)
    , runPAB
    , PABEnvironment(appEnv)
    -- * Logging
    , logString
    , logPretty
    -- * Contract instances
    , activateContract
    , callEndpointOnInstance
    , payToPublicKey
    -- * Querying the state
    , instanceState
    , observableState
    , waitForState
    , activeEndpoints
    , waitForEndpoint
    , currentSlot
    , waitUntilSlot
    , waitNSlots
    , activeContracts
    , finalResult
    , waitUntilFinished
    , userEnv
    -- * Run PAB effects in separate threads
    , PABRunner(..)
    , pabRunner
    -- * Other stuff (TODO: Move to Plutus.PAB.App)
    , dbConnect
    , installContract
    , activateContractSTM
    , reportContractState
    , Connection(Connection)
    , toUUID
    -- * Effect handlers
    , AppMsg(..)
    , handleMappedReader
    , handleUserEnvReader
    , handleBlockchainEnvReader
    , handleInstancesStateReader
    , timed
    ) where

import           Control.Concurrent.STM                          (STM)
import qualified Control.Concurrent.STM                          as STM
import           Control.Monad                                   (forM, guard, void)
import           Control.Monad.Freer                             (Eff, Member, interpret, reinterpret, runM, send,
                                                                  subsume, type (~>))
import           Control.Monad.Freer.Error                       (Error, runError)
import           Control.Monad.Freer.Extras.Log                  (LogMessage, LogMsg (..), LogObserve, handleObserveLog,
                                                                  logInfo, mapLog)
import qualified Control.Monad.Freer.Extras.Modify               as Modify
import           Control.Monad.Freer.Reader                      (Reader (..), ask, asks, runReader)
import           Control.Monad.IO.Class                          (MonadIO (..))
import           Control.Monad.IO.Unlift                         (MonadUnliftIO)
import           Control.Monad.Logger                            (MonadLogger)
import qualified Control.Monad.Logger                            as MonadLogger
import           Data.Aeson                                      (FromJSON, ToJSON (..))
import qualified Data.Aeson                                      as JSON
import qualified Data.Map                                        as Map
import           Data.Set                                        (Set)
import           Data.Text                                       (Text)
import qualified Data.Text                                       as Text
import           Data.Text.Prettyprint.Doc                       (Pretty, colon, defaultLayoutOptions, layoutPretty,
                                                                  pretty, (<+>))
import qualified Data.Text.Prettyprint.Doc.Render.Text           as Render
import           Database.Persist.Sqlite                         (createSqlitePoolFromInfo, mkSqliteConnectionInfo)
import           Eventful.Store.Sql                              (defaultSqlEventStoreConfig)
import           GHC.Generics                                    (Generic)
import           Language.Plutus.Contract.Effects.ExposeEndpoint (ActiveEndpoint (..))
import           Ledger.Tx                                       (Tx)
import           Ledger.Value                                    (Value)
import           Plutus.PAB.Core.ContractInstance                (ContractInstanceMsg, activateContractSTM)
import qualified Plutus.PAB.Core.ContractInstance                as ContractInstance
import           Plutus.PAB.Core.ContractInstance.STM            (BlockchainEnv, InstancesState, OpenEndpoint (..))
import qualified Plutus.PAB.Core.ContractInstance.STM            as Instances
import           Plutus.PAB.Effects.Contract                     (ContractDefinitionStore, ContractEffect,
                                                                  ContractStore, PABContract (..), addDefinition,
                                                                  getState)
import qualified Plutus.PAB.Effects.Contract                     as Contract
import qualified Plutus.PAB.Effects.ContractRuntime              as ContractRuntime
import           Plutus.PAB.Effects.EventLog                     (Connection (..))
import qualified Plutus.PAB.Effects.EventLog                     as EventLog
import           Plutus.PAB.Effects.UUID                         (UUIDEffect, handleUUIDEffect)
import           Plutus.PAB.Events.Contract                      (ContractPABRequest)
import           Plutus.PAB.Events.ContractInstanceState         (PartiallyDecodedResponse)
import           Plutus.PAB.Monitoring.PABLogMsg                 (CoreMsg (..), PABLogMsg (..), PABMultiAgentMsg (..))
import           Plutus.PAB.Types                                (DbConfig (DbConfig), PABError, dbConfigFile,
                                                                  dbConfigPoolSize, toUUID)
import           Wallet.API                                      (PubKey, Slot)
import qualified Wallet.API                                      as WAPI
import           Wallet.Effects                                  (ChainIndexEffect, ContractRuntimeEffect,
                                                                  NodeClientEffect, WalletEffect)
import           Wallet.Emulator.LogMessages                     (RequestHandlerLogMsg, TxBalanceMsg)
import           Wallet.Emulator.MultiAgent                      (EmulatorEvent' (..), EmulatorTimeEvent (..))
import           Wallet.Emulator.Wallet                          (Wallet, WalletEvent (..))
import           Wallet.Types                                    (ContractInstanceId, EndpointDescription (..),
                                                                  NotificationError)


type PABEffects t env =
    '[ ContractStore t
     , ContractEffect t
     , LogMsg (PABMultiAgentMsg t)
     , Reader (PABEnvironment t env)
     , Error PABError
     , IO
     ]

type PABAction t env a = Eff (PABEffects t env) a

newtype PABRunner t env = PABRunner { runPABAction :: forall a. PABAction t env a -> IO (Either PABError a) }

-- | Shared data that is needed by all PAB threads.
data PABEnvironment t env =
    PABEnvironment
        { instancesState :: InstancesState
        , blockchainEnv  :: BlockchainEnv
        , appEnv         :: env
        , effectHandlers :: EffectHandlers t env
        }

-- | Get a 'PABRunner' that uses the current environment.
pabRunner :: forall t env. PABAction t env (PABRunner t env)
pabRunner = do
    h@PABEnvironment{effectHandlers=EffectHandlers{handleLogMessages, handleContractStoreEffect, handleContractEffect}} <- ask @(PABEnvironment t env)
    pure $ PABRunner $ \action -> do
        runM
            $ runError
            $ runReader h
            $ handleLogMessages
            $ handleContractEffect
            $ handleContractStoreEffect
            $ action

-- | Top-level entry point. Run a 'PABAction', using the 'EffectHandlers' to deal with logs,
--   startup and shutdown, etc.
runPAB ::
    forall t env a.
    EffectHandlers t env
    -> PABAction t env a
    -> IO (Either PABError a)
runPAB effectHandlers action = runM $ runError $ do
    let EffectHandlers{initialiseEnvironment, onStartup, onShutdown, handleLogMessages, handleContractStoreEffect, handleContractEffect} = effectHandlers
    (instancesState, blockchainEnv, appEnv) <- initialiseEnvironment
    let env = PABEnvironment{instancesState, blockchainEnv, appEnv, effectHandlers}

    runReader env $ handleLogMessages $ handleContractEffect $ handleContractStoreEffect $ do
        onStartup
        result <- action
        onShutdown
        pure result

-- | Start a new instance of a contract
activateContract :: forall t env. PABContract t => Wallet -> ContractDef t -> PABAction t env ContractInstanceId
activateContract w def = do
    PABRunner{runPABAction} <- pabRunner

    let handler :: forall a. Eff (ContractInstanceEffects t env '[IO]) a -> IO a
        handler x = fmap (either (error . show) id) (runPABAction $ handleAgentThread w x)
    handleAgentThread w
        $ ContractInstance.activateContractSTM @t @IO @(ContractInstanceEffects t env '[IO]) handler def

-- | Call a named endpoint on a contract instance
callEndpointOnInstance ::
    forall t env a.
    ( JSON.ToJSON a
    )
    => ContractInstanceId
    -> String
    -> a
    -> PABAction t env (Maybe NotificationError)
callEndpointOnInstance instanceID ep value = do
    state <- asks @(PABEnvironment t env) instancesState
    liftIO $ STM.atomically $ Instances.callEndpointOnInstance state (EndpointDescription ep) (JSON.toJSON value) instanceID


-- | Make a payment to a public key
payToPublicKey :: Wallet -> PubKey -> Value -> PABAction t env Tx
payToPublicKey source target amount =
    handleAgentThread source $ WAPI.payToPublicKey WAPI.defaultSlotRange amount target

-- | Effects available to contract instances that run in their own thread
type ContractInstanceEffects t env effs =
    ContractRuntimeEffect
    ': ContractEffect t
    ': ContractStore t
    ': WalletEffect
    ': ChainIndexEffect
    ': NodeClientEffect
    ': UUIDEffect
    ': LogMsg TxBalanceMsg
    ': LogMsg RequestHandlerLogMsg
    ': LogMsg (ContractInstanceMsg t)
    ': LogObserve (LogMessage Text)
    ': LogMsg Text
    ': Error PABError
    ': Reader BlockchainEnv
    ': Reader InstancesState
    ': Reader (PABEnvironment t env)
    ': Reader Wallet
    ': effs

-- | Handle
handleAgentThread ::
    forall t env a.
    Wallet
    -> Eff (ContractInstanceEffects t env '[IO]) a
    -> PABAction t env a
handleAgentThread wallet action = do
    PABEnvironment{effectHandlers, blockchainEnv, instancesState} <- ask @(PABEnvironment t env)
    let EffectHandlers{handleContractStoreEffect, handleContractEffect, handleServicesEffects} = effectHandlers
    let action' :: Eff (ContractInstanceEffects t env (IO ': PABEffects t env)) a = Modify.raiseEnd action

    subsume @IO
        $ runReader wallet
        $ subsume @(Reader (PABEnvironment t env))
        $ runReader instancesState
        $ runReader blockchainEnv
        $ subsume @(Error PABError)
        $ (interpret (mapLog @_ @(PABMultiAgentMsg t) EmulatorMsg) . reinterpret (timed @EmulatorEvent' @t @env) . reinterpret (mapLog (WalletEvent wallet)) . reinterpret (mapLog GenericLog))
        $ handleObserveLog
        $ interpret (mapLog ContractInstanceLog)
        $ (interpret (mapLog @_ @(PABMultiAgentMsg t) EmulatorMsg) . reinterpret (timed @EmulatorEvent' @t @env) . reinterpret (mapLog (WalletEvent wallet)) . reinterpret (mapLog RequestHandlerLog))
        $ (interpret (mapLog @_ @(PABMultiAgentMsg t) EmulatorMsg) . reinterpret (timed @EmulatorEvent' @t @env) . reinterpret (mapLog (WalletEvent wallet)) . reinterpret (mapLog TxBalanceLog))
        $ handleUUIDEffect
        $ handleServicesEffects wallet
        $ handleContractStoreEffect
        $ handleContractEffect
        $ (handleContractRuntimeMsg @t . reinterpret @ContractRuntimeEffect @(LogMsg ContractRuntime.ContractRuntimeMsg) ContractRuntime.handleContractRuntime)
        $ action'


-- | Effect handlers for running the PAB.
data EffectHandlers t env =
    EffectHandlers
        { -- | Create the initial environment. This value is shared between all threads
          --   started by the PAB.
          initialiseEnvironment :: forall m effs.
            ( Member (Error PABError) effs
            , MonadIO (Eff effs)
            )
            => Eff effs (InstancesState, BlockchainEnv, env)

        -- | Handle log messages
        , handleLogMessages :: forall m effs.
            ( Member (Reader (PABEnvironment t env)) effs
            , Member (Error PABError) effs
            , MonadIO (Eff effs)
            )
            => Eff (LogMsg (PABMultiAgentMsg t) ': effs)
            ~> Eff effs

        -- | Handle the 'ContractStore' effect
        , handleContractStoreEffect :: forall m effs.
            ( Member (Reader (PABEnvironment t env)) effs
            , Member (Error PABError) effs
            , Member (LogMsg (PABMultiAgentMsg t)) effs
            , MonadIO (Eff effs)
            )
            => Eff (ContractStore t ': effs)
            ~> Eff effs

        -- | Handle the 'ContractEffect'
        , handleContractEffect :: forall m effs.
            ( Member (Reader (PABEnvironment t env)) effs
            , Member (Error PABError) effs
            , Member (LogMsg (PABMultiAgentMsg t)) effs
            , MonadIO (Eff effs)
            )
            => Eff (ContractEffect t ': effs)
            ~> Eff effs

        -- | Handle effects that serve requests to external services managed by the PAB
        --   Runs in the context of a particular wallet.
        , handleServicesEffects :: forall m effs.
            ( Member (Reader (PABEnvironment t env)) effs
            , Member (Error PABError) effs
            , Member (LogMsg (PABMultiAgentMsg t)) effs
            , MonadIO (Eff effs)
            )
            => Wallet
            -> Eff (WalletEffect ': ChainIndexEffect ': NodeClientEffect ': effs)
            ~> Eff effs

        -- | Action to run on startup
        , onStartup :: PABAction t env ()

        -- | Action to run on shutdown
        , onShutdown :: PABAction t env ()
        }

-- applicationHandlers :: EffectHandlers ContractExe ()
-- applicationHandlers = undefined

installContract ::
    forall t effs.
    ( Member (LogMsg (CoreMsg (ContractDef t))) effs
    , Member (ContractDefinitionStore t) effs
    )
    => (ContractDef t)
    -> Eff effs ()
installContract contractHandle = do
    logInfo @(CoreMsg (ContractDef t)) $ Installing contractHandle
    addDefinition @t contractHandle
    logInfo @(CoreMsg (ContractDef t)) Installed

reportContractState ::
    forall t effs.
    ( Member (LogMsg (CoreMsg t)) effs
    , Member (ContractStore t) effs
    , State t ~ PartiallyDecodedResponse ContractPABRequest
    )
    => ContractInstanceId
    -> Eff effs ()
reportContractState cid = do
    logInfo @(CoreMsg t) $ FindingContract cid
    contractState <- getState @t cid
    logInfo @(CoreMsg t) $ FoundContract $ Just contractState

------------------------------------------------------------
-- | Create a database 'Connection' containing the connection pool
-- plus some configuration information.
dbConnect ::
    ( MonadUnliftIO m
    , MonadLogger m
    )
    => DbConfig
    -> m EventLog.Connection
dbConnect DbConfig {dbConfigFile, dbConfigPoolSize} = do
    let connectionInfo = mkSqliteConnectionInfo dbConfigFile
    MonadLogger.logDebugN "Connecting to DB"
    connectionPool <- createSqlitePoolFromInfo connectionInfo dbConfigPoolSize
    pure $ EventLog.Connection (defaultSqlEventStoreConfig, connectionPool)

data AppMsg t =
    InstalledContractsMsg
    | ActiveContractsMsg
    | TransactionHistoryMsg
    | ContractHistoryMsg
    | ProcessInboxMsg
    | PABMsg PABLogMsg
    | InstalledContract Text
    | ContractInstances (ContractDef t) [ContractInstanceId]
    | TxHistoryItem Tx
    | ContractHistoryItem Int (PartiallyDecodedResponse ContractPABRequest)
    deriving stock (Generic)

deriving stock instance (Show (ContractDef t)) => Show (AppMsg t)
deriving anyclass instance (ToJSON (ContractDef t)) => ToJSON (AppMsg t)
deriving anyclass instance (FromJSON (ContractDef t)) => FromJSON (AppMsg t)


instance Pretty (ContractDef t) => Pretty (AppMsg t) where
    pretty = \case
        InstalledContractsMsg   -> "Installed contracts"
        ActiveContractsMsg      -> "Active contracts"
        TransactionHistoryMsg   -> "Transaction history"
        ContractHistoryMsg      -> "Contract history"
        ProcessInboxMsg         -> "Process contract inbox"
        PABMsg m                -> pretty m
        InstalledContract t     -> pretty t
        ContractInstances t s   -> pretty t <+> pretty s
        TxHistoryItem t         -> pretty t
        ContractHistoryItem i s -> pretty i <> colon <+> pretty s

-- | Annotate log messages with the current slot number.
timed ::
    forall e t env effs.
    ( Member (LogMsg (EmulatorTimeEvent e)) effs
    , Member (Reader (PABEnvironment t env)) effs
    , MonadIO (Eff effs)
    )
    => LogMsg e
    ~> Eff effs
timed = \case
    LMessage m -> do
        m' <- forM m $ \msg -> do
            sl <- asks @(PABEnvironment t env) (Instances.beCurrentSlot . blockchainEnv) >>= liftIO . STM.readTVarIO
            pure (EmulatorTimeEvent sl msg)
        send (LMessage m')

handleContractRuntimeMsg :: forall t x effs. Member (LogMsg (PABMultiAgentMsg t)) effs => Eff (LogMsg ContractRuntime.ContractRuntimeMsg ': effs) x -> Eff effs x
handleContractRuntimeMsg = interpret (mapLog @_ @(PABMultiAgentMsg t) RuntimeLog)

-- | Log some output to the console
logString :: forall t effs. Member (LogMsg (PABMultiAgentMsg t)) effs => String -> Eff effs ()
logString = logInfo @(PABMultiAgentMsg t) . UserLog . Text.pack

-- | Pretty-prin a value to the console
logPretty :: forall a t effs. (Pretty a, Member (LogMsg (PABMultiAgentMsg t)) effs) => a -> Eff effs ()
logPretty = logInfo @(PABMultiAgentMsg t) . UserLog . render

render :: forall a. Pretty a => a -> Text
render = Render.renderStrict . layoutPretty defaultLayoutOptions . pretty

-- | Get the current state of the contract instance.
instanceState :: forall t env. Wallet -> ContractInstanceId -> PABAction t env (Contract.State t)
instanceState wallet instanceId = handleAgentThread wallet (Contract.getState @t instanceId)

-- | An STM transaction that returns the observable state of the contract instance.
observableState :: forall t env. ContractInstanceId -> PABAction t env (STM JSON.Value)
observableState instanceId = do
    instancesState <- asks @(PABEnvironment t env) instancesState
    pure $ Instances.obervableContractState instanceId instancesState

-- | Wait until the observable state of the instance matches a predicate.
waitForState :: forall t env a. (JSON.Value -> Maybe a) -> ContractInstanceId -> PABAction t env a
waitForState extract instanceId = do
    stm <- observableState instanceId
    liftIO $ STM.atomically $ do
        state <- stm
        case extract state of
            Nothing -> STM.retry
            Just k  -> pure k

-- | The list of endpoints that are currently open
activeEndpoints :: forall t env. ContractInstanceId -> PABAction t env (STM [OpenEndpoint])
activeEndpoints instanceId = do
    instancesState <- asks @(PABEnvironment t env) instancesState
    pure $ do
        is <- Instances.instanceState instanceId instancesState
        fmap snd . Map.toList <$> Instances.openEndpoints is

-- | Wait until the endpoint becomes active.
waitForEndpoint :: forall t env. ContractInstanceId -> String -> PABAction t env ()
waitForEndpoint instanceId endpointName = do
    tx <- activeEndpoints instanceId
    liftIO $ STM.atomically $ do
        eps <- tx
        guard $ any (\Instances.OpenEndpoint{Instances.oepName=ActiveEndpoint{aeDescription=EndpointDescription nm}} -> nm == endpointName) eps

currentSlot :: forall t env. PABAction t env (STM Slot)
currentSlot = do
    Instances.BlockchainEnv{Instances.beCurrentSlot} <- asks @(PABEnvironment t env) blockchainEnv
    pure $ STM.readTVar beCurrentSlot

-- | Wait until the target slot number has been reached
waitUntilSlot :: forall t env. Slot -> PABAction t env ()
waitUntilSlot targetSlot = do
    tx <- currentSlot
    void $ liftIO $ STM.atomically $ do
        s <- tx
        guard (s >= targetSlot)

waitNSlots :: forall t env. Int -> PABAction t env ()
waitNSlots i = do
    current <- currentSlot >>= liftIO . STM.atomically
    waitUntilSlot (current + fromIntegral i)

-- | The set of all active contracts.
activeContracts :: forall t env. PABAction t env (Set ContractInstanceId)
activeContracts = do
    instancesState <- asks @(PABEnvironment t env) instancesState
    liftIO $ STM.atomically $ Instances.instanceIDs instancesState

-- | The final result of the instance (waits until it is available)
finalResult :: forall t env. ContractInstanceId -> PABAction t env (STM (Maybe JSON.Value))
finalResult instanceId = do
    instancesState <- asks @(PABEnvironment t env) instancesState
    pure $ Instances.finalResult instanceId instancesState

-- | Wait until the contract is done, then return
--   the error (if any)
waitUntilFinished :: forall t env. ContractInstanceId -> PABAction t env (Maybe JSON.Value)
waitUntilFinished i =
    finalResult i >>= liftIO . STM.atomically

-- | Read the 'env' from the environment
userEnv :: forall t env effs. Member (Reader (PABEnvironment t env)) effs => Eff effs env
userEnv = interpret (handleUserEnvReader @t @env) ask

handleMappedReader :: forall f g effs.
    Member (Reader f) effs
    => (f -> g)
    -> Reader g
    ~> Eff effs
handleMappedReader f = \case
    Ask -> asks @f f

handleUserEnvReader :: forall t env effs.
    Member (Reader (PABEnvironment t env)) effs
    => Reader env
    ~> Eff effs
handleUserEnvReader = \case
    Ask -> asks @(PABEnvironment t env) appEnv

handleBlockchainEnvReader :: forall t env effs.
    Member (Reader (PABEnvironment t env)) effs
    => Reader BlockchainEnv
    ~> Eff effs
handleBlockchainEnvReader = \case
    Ask -> asks @(PABEnvironment t env) blockchainEnv

handleInstancesStateReader :: forall t env effs.
    Member (Reader (PABEnvironment t env)) effs
    => Reader InstancesState
    ~> Eff effs
handleInstancesStateReader = \case
    Ask -> asks @(PABEnvironment t env) instancesState
