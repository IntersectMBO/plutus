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
    ) where

import qualified Control.Concurrent.STM                  as STM
import           Control.Monad.Freer                     (Eff, LastMember, Member, interpret, reinterpret, runM,
                                                          subsume, type (~>))
import           Control.Monad.Freer.Error               (Error, runError)
import           Control.Monad.Freer.Extras.Log          (LogMessage, LogMsg (..), LogObserve, logInfo, mapLog)
import qualified Control.Monad.Freer.Extras.Modify       as Modify
import           Control.Monad.Freer.Reader              (Reader, ask, runReader)
import           Control.Monad.IO.Class                  (MonadIO (..))
import           Control.Monad.IO.Unlift                 (MonadUnliftIO)
import           Control.Monad.Logger                    (MonadLogger)
import qualified Control.Monad.Logger                    as MonadLogger
import           Data.Aeson                              (FromJSON, ToJSON (..))
import           Data.Text                               (Text)
import           Data.Text.Prettyprint.Doc               (Pretty, colon, pretty, (<+>))
import           Database.Persist.Sqlite                 (createSqlitePoolFromInfo, mkSqliteConnectionInfo)
import           Eventful.Store.Sql                      (defaultSqlEventStoreConfig)
import           GHC.Generics                            (Generic)
import           Ledger.Tx                               (Tx)
import           Plutus.PAB.Core.ContractInstance        (ContractInstanceMsg, activateContractSTM)
import           Plutus.PAB.Core.ContractInstance.STM    (BlockchainEnv, InstancesState)
import qualified Plutus.PAB.Core.ContractInstance.STM    as Instances
import           Plutus.PAB.Effects.Contract             (ContractDefinitionStore, ContractEffect, ContractStore,
                                                          PABContract (..), addDefinition, getState)
import qualified Plutus.PAB.Effects.ContractRuntime      as ContractRuntime
import           Plutus.PAB.Effects.EventLog             (Connection (..))
import qualified Plutus.PAB.Effects.EventLog             as EventLog
import           Plutus.PAB.Effects.UUID                 (UUIDEffect, handleUUIDEffect)
import           Plutus.PAB.Events.Contract              (ContractPABRequest)
import           Plutus.PAB.Events.ContractInstanceState (PartiallyDecodedResponse)
import           Plutus.PAB.Monitoring.PABLogMsg         (ContractEffectMsg, CoreMsg (..), PABLogMsg (..),
                                                          PABMultiAgentMsg (..))
import           Plutus.PAB.Types                        (DbConfig (DbConfig), PABError, dbConfigFile, dbConfigPoolSize,
                                                          toUUID)
import           Wallet.Effects                          (ChainIndexEffect, ContractRuntimeEffect, NodeClientEffect,
                                                          WalletEffect)
import qualified Wallet.Emulator.Chain                   as Chain
import           Wallet.Emulator.LogMessages             (RequestHandlerLogMsg, TxBalanceMsg)
import           Wallet.Emulator.MultiAgent              (EmulatorEvent' (..), EmulatorTimeEvent (..), _singleton)
import           Wallet.Emulator.Wallet                  (Wallet)
import           Wallet.Types                            (ContractInstanceId)


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
activateContract :: forall t env a. PABContract t => Wallet -> ContractDef t -> PABAction t env ContractInstanceId
activateContract w def = undefined

    -- let handler :: forall a. Eff (AgentEffects '[IO]) a -> IO a
    --     handler x = fmap (either (error . show) id) (handleAgentThread simState blockchainEnv instancesState w x)
    -- ContractInstance.activateContractSTM @TestContracts @IO @(AgentEffects '[IO]) handler def

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
    ': Reader env
    ': Reader InstancesState
    ': Reader BlockchainEnv
    ': Reader Wallet
    ': effs

-- | Handle
handleAgentThread ::
    forall t env a.
    Wallet
    -> Eff (ContractInstanceEffects t env '[IO]) a
    -> PABAction t env a
handleAgentThread wallet action = do
    e@PABEnvironment{effectHandlers, instancesState, blockchainEnv, appEnv} <- ask @(PABEnvironment t env)
    let EffectHandlers{handleLogMessages} = effectHandlers
    let action' :: Eff (ContractInstanceEffects t env '[IO, LogMsg (PABMultiAgentMsg t), Error PABError, Reader (PABEnvironment t env), IO]) a = Modify.raiseEnd action
        makeTimedWalletEvent wllt =
            interpret (mapLog @_ @(PABMultiAgentMsg t) EmulatorMsg)
            . reinterpret (timed @EmulatorEvent')
            . reinterpret (mapLog (WalletEvent wllt))
        makeTimedChainEvent =
            interpret (mapLog @_ @(PABMultiAgentMsg t) EmulatorMsg)
            . reinterpret (timed @EmulatorEvent')
            . reinterpret (mapLog ChainEvent)
        makeTimedChainIndexEvent wllt =
            interpret (mapLog @_ @(PABMultiAgentMsg t) EmulatorMsg)
            . reinterpret (timed @EmulatorEvent')
            . reinterpret (mapLog (ChainIndexEvent wllt))

    runM
        $ runReader e
        $ runError
        $ interpret handleLogMessages
        $ subsume @IO
        $ subsume @(Reader env)
        $ runReader wallet
        $ runReader blockchainEnv
        $ runReader instancesState
        $ subsume @(Error PABError)
        $ (makeTimedWalletEvent wallet . reinterpret (mapLog GenericLog))
        $ handleObserveLog
        $ interpret (mapLog ContractInstanceLog)
        $ (makeTimedWalletEvent wallet . reinterpret (mapLog RequestHandlerLog))
        $ (makeTimedWalletEvent wallet . reinterpret (mapLog TxBalanceLog))

        $ handleUUIDEffect

        -- $ makeTimedChainEvent
        -- $ reinterpret @_ @(LogMsg Chain.ChainEvent) handleChainEffect

        -- $ interpret handleNodeClient

        -- $ makeTimedChainIndexEvent wallet
        -- $ reinterpret @_ @(LogMsg ChainIndex.ChainIndexEvent) handleChainIndexEffect

        -- $ flip (handleError @WAPI.WalletAPIError) (throwError @PABError . WalletError)
        -- $ interpret (runWalletState wallet)
        -- $ reinterpret2 @_ @(State Wallet.WalletState) @(Error WAPI.WalletAPIError) Wallet.handleWallet

        $ handleServicesEffects

        $ interpret @(ContractStore t) handleContractStore

        $ handleContractEffectMsg @t
        $ reinterpret @(ContractEffect t) @(LogMsg ContractEffectMsg) handleContractTest

        $ handleContractRuntimeMsg @t
        $ reinterpret @ContractRuntimeEffect @(LogMsg ContractRuntime.ContractRuntimeMsg) ContractRuntime.handleContractRuntime

        $ action'


-- | Effect handlers for running the PAB.
data EffectHandlers t env =
    EffectHandlers
        { -- | Create the initial environment. This value is shared between all threads
          --   started by the PAB.
          initialiseEnvironment :: forall m effs.
            ( Member (Error PABError) effs
            , MonadIO m
            , LastMember m effs
            )
            => Eff effs (InstancesState, BlockchainEnv, env)

        -- | Handle log messages
        , handleLogMessages :: forall m effs.
            ( Member (Reader (PABEnvironment t env)) effs
            , Member (Error PABError) effs
            , MonadIO m
            , LastMember m effs
            )
            => Eff (LogMsg (PABMultiAgentMsg t) ': effs)
            ~> Eff effs

        -- | Handle the 'ContractStore' effect
        , handleContractStoreEffect :: forall m effs.
            ( Member (Reader (PABEnvironment t env)) effs
            , Member (Error PABError) effs
            , Member (LogMsg (PABMultiAgentMsg t)) effs
            , MonadIO m
            , LastMember m effs
            )
            => Eff (ContractStore t ': effs)
            ~> Eff effs

        -- | Handle the 'ContractEffect'
        , handleContractEffect :: forall m effs.
            ( Member (Reader (PABEnvironment t env)) effs
            , Member (Error PABError) effs
            , Member (LogMsg (PABMultiAgentMsg t)) effs
            , MonadIO m
            , LastMember m effs
            )
            => Eff (ContractEffect t ': effs)
            ~> Eff effs

        -- | Handle effects that serve requests to external services managed by the PAB
        --   Runs in the context of a particular wallet (note the 'Reader Wallet' effect)
        , handleServicesEffects :: forall m effs.
            ( Member (Reader (PABEnvironment t env)) effs
            , Member (Error PABError) effs
            , Member (LogMsg (PABMultiAgentMsg t)) effs
            , Member (Reader Wallet) effs
            , MonadIO m
            , LastMember m effs
            )
            => Eff (WalletEffect ': NodeClientEffect ': ChainIndexEffect ': effs)
            ~> Eff effs

        -- | Action to run on startup
        , onStartup :: PABAction t env ()

        -- | Action to run on shutdown
        , onShutdown :: PABAction t env ()
        }

-- -- | 'EffectHandlers' for running the PAB as a simulator (no connectivity to
-- --   out-of-process services such as wallet backend, node, etc.)
-- simulatorHandlers :: EffectHandlers TestContracts (SimulatorState TestContracts)
-- simulatorHandlers =
--     EffectHandlers
--         { initialiseEnvironment = liftIO Simulator.initialState
--         , handleContractStoreEffect =
--             interpret handleContractStore
--         , handleContractEffect =
--             handleContractTestMsg
--             . reinterpret handleContractTest
--         , handleLogMessages = undefined -- FIXME
--         , handleServicesEffects = undefined -- FIXME
--         , onStartup = pure () -- FIXME: Start clock thread
--         , onShutdown = pure ()
--         }

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
    forall e m effs.
    ( Member (LogMsg (EmulatorTimeEvent e)) effs
    , Member (Reader BlockchainEnv) effs
    , LastMember m effs
    , MonadIO m
    )
    => LogMsg e
    ~> Eff effs
timed = \case
    LMessage m -> do
        m' <- forM m $ \msg -> do
            sl <- asks @Instances.BlockchainEnv Instances.beCurrentSlot >>= liftIO . STM.readTVarIO
            pure (EmulatorTimeEvent sl msg)
        send (LMessage m')
