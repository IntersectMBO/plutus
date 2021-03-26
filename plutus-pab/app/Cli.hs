{-# LANGUAGE ApplicativeDo         #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DerivingVia           #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns        #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE RecordWildCards       #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeOperators         #-}

module Cli (runCliCommand) where

-----------------------------------------------------------------------------------------------------------------------
-- Command interpretation
-----------------------------------------------------------------------------------------------------------------------

{- Note [Use of iohk-monitoring in PAB]

We use the 'iohk-monitoring' package to process the log messages that come
out of the 'Control.Monad.Freer.Log' effects. We create a top-level 'Tracer'
value that we pass to 'Plutus.PAB.Monitoring.Monitoring.handleLogMsgTrace', which
ultimately runs the trace actions in IO.

This works well for our own code that uses the 'freer-simple' effects, but in
order to get our dependencies to work together we need to do a bit more work:
The SQLite backend for eventful uses 'mtl' and requires a 'MonadLogger' instance
for the monad that it runs in.

My first thought was to define an instance

@Member (LogMsg MonadLoggerMsg effs) => MonadLogger (Eff effs)@

similar to the 'MonadIO' instance for 'Control.Monad.Freer.Eff' [1]. This
works, but it doesn't solve the problem because the sqlite backend *also*
requires an instance of 'MonadUnliftIO'. The only way I was able to provide
this instance was by pulling both 'MonadLogger' and 'MonadUnliftIO' into the
base monad of the 'AppBackend' effects stack.

The 'MonadLogger' and 'MonadUnliftIO' constraints propagate up to the top level
via 'Plutus.PAB.Effects.EventLog.handleEventLogSql'. Both instances are
provided by 'Plutus.PAB.Monitoring.MonadLoggerBridge.TraceLoggerT', which translates
'MonadLogger' calls to 'Tracer' calls. This is why the base monad of the
effects stack in 'runCliCommand' is 'TraceLoggerT IO' instead of just 'IO'.

We have to use 'natTracer' in some places to turn 'Trace IO a' into
'Trace (TraceLoggerT IO) a'.

[1] https://hackage.haskell.org/package/freer-simple-1.2.1.1/docs/Control-Monad-Freer.html#t:Eff

-}


import           Command

import           Cardano.BM.Configuration                 (Configuration)
import qualified Cardano.BM.Configuration.Model           as CM
import           Cardano.BM.Data.Trace                    (Trace)
import qualified Cardano.ChainIndex.Server                as ChainIndex
import qualified Cardano.Metadata.Server                  as Metadata
import qualified Cardano.Node.Server                      as NodeServer
import qualified Cardano.Wallet.Server                    as WalletServer
import           Cardano.Wallet.Types
import           Control.Concurrent.Async                 (Async, async, waitAny)
import           Control.Concurrent.Availability          (Availability, starting)
import           Control.Monad                            (void)
import           Control.Monad.Freer                      (interpret)
import           Control.Monad.Freer.Extras.Log           (logInfo)
import           Control.Monad.IO.Class                   (liftIO)
import           Data.Foldable                            (traverse_)
import qualified Data.Map                                 as Map
import           Data.Proxy                               (Proxy (..))
import qualified Data.Set                                 as Set
import           Data.Text.Prettyprint.Doc                (Pretty (..), defaultLayoutOptions, layoutPretty, pretty)
import           Data.Text.Prettyprint.Doc.Render.Text    (renderStrict)
import qualified Plutus.PAB.Effects.Contract              as Contract

import           Cardano.Node.Types                       (MockServerConfig (..))
import qualified PSGenerator
import           Plutus.Contract.Resumable                (responses)
import           Plutus.Contract.State                    (State (..))
import           Plutus.Contracts.Currency                (SimpleMPS (..))
import qualified Plutus.PAB.App                           as App
import qualified Plutus.PAB.Core                          as Core
import qualified Plutus.PAB.Db.Eventful                   as Eventful
import           Plutus.PAB.Effects.Contract.ContractExe  (ContractExe)
import           Plutus.PAB.Effects.Contract.ContractTest (TestContracts (Currency))
import           Plutus.PAB.Events.ContractInstanceState  (PartiallyDecodedResponse (..))
import qualified Plutus.PAB.Monitoring.Monitoring         as LM
import qualified Plutus.PAB.Simulator                     as Simulator
import           Plutus.PAB.Types                         (Config (..), chainIndexConfig, metadataServerConfig,
                                                           nodeServerConfig, requestProcessingConfig,
                                                           walletServerConfig)
import qualified Plutus.PAB.Webserver.Server              as PABServer
import           Plutus.PAB.Webserver.Types               (ContractActivationArgs (..))
import           Wallet.Emulator.Wallet                   (Wallet (..))

-- | Interpret a 'Command' in 'Eff' using the provided tracer and configurations
--
runCliCommand ::
    Trace IO (LM.AppMsg ContractExe)  -- ^ PAB Tracer logging instance
    -> Configuration -- ^ Monitoring configuration
    -> Config        -- ^ PAB Configuration
    -> Availability  -- ^ Token for signaling service availability
    -> Command
    -> IO ()

-- Run database migration
runCliCommand t _ Config{dbConfig} _ Migrate =
    App.migrate (LM.convertLog LM.PABMsg t) dbConfig

-- Run mock wallet service
runCliCommand trace _ Config {..} serviceAvailability MockWallet =
    liftIO $ WalletServer.main
        (toWalletLog trace)
        walletServerConfig
        (mscSocketPath nodeServerConfig)
        (ChainIndex.ciBaseUrl chainIndexConfig)
        serviceAvailability

-- Run mock node server
runCliCommand trace _ Config {nodeServerConfig} serviceAvailability MockNode =
    liftIO $ NodeServer.main
        (toMockNodeServerLog trace)
        nodeServerConfig
        serviceAvailability

-- Run mock metadata server
runCliCommand trace _ Config {metadataServerConfig} serviceAvailability Metadata =
    liftIO $ Metadata.main
        (toMetaDataLog trace)
        metadataServerConfig
        serviceAvailability

-- Run PAB webserver
runCliCommand trace _ config@Config{pabWebserverConfig} serviceAvailability PABWebserver =
        fmap (either (error . show) id)
        $ App.runApp (toPABMsg trace) config
        $ do
            App.AppEnv{App.walletClientEnv} <- Core.askUserEnv @ContractExe @App.AppEnv
            shutdown <- PABServer.startServer pabWebserverConfig (Left walletClientEnv) serviceAvailability
            _ <- liftIO getLine
            shutdown

-- Fork a list of commands
runCliCommand trace logConfig config serviceAvailability (ForkCommands commands) =
    void $ do
        threads <- traverse forkCommand commands
        putStrLn "Started all commands."
        waitAny threads
  where
    forkCommand ::  Command -> IO (Async ())
    forkCommand subcommand = do
      putStrLn $ "Starting: " <> show subcommand
      asyncId <- async . void . runCliCommand trace logConfig config serviceAvailability $ subcommand
      putStrLn $ "Started: " <> show subcommand
      starting serviceAvailability
      pure asyncId

-- Run the chain-index service
runCliCommand t _ Config {nodeServerConfig, chainIndexConfig} serviceAvailability ChainIndex =
    ChainIndex.main
        (toChainIndexLog t)
        chainIndexConfig
        (mscSocketPath nodeServerConfig)
        serviceAvailability

-- Install a contract
runCliCommand t _ Config{dbConfig} _ (InstallContract contractExe) = do
    connection <- App.dbConnect (LM.convertLog LM.PABMsg t) dbConfig
    fmap (either (error . show) id)
        $ Eventful.runEventfulStoreAction connection (LM.convertLog (LM.PABMsg . LM.SLoggerBridge) t)
        $ Contract.addDefinition @ContractExe contractExe

-- Get the state of a contract
runCliCommand t _ Config{dbConfig} _ (ContractState contractInstanceId) = do
    connection <- App.dbConnect (LM.convertLog LM.PABMsg t) dbConfig
    fmap (either (error . show) id)
        $ Eventful.runEventfulStoreAction connection (LM.convertLog (LM.PABMsg . LM.SLoggerBridge) t)
        $ interpret (LM.handleLogMsgTrace t)
        $ do
            s <- Contract.getState @ContractExe contractInstanceId
            let outputState = Contract.serialisableState (Proxy @ContractExe) s
            logInfo @(LM.AppMsg ContractExe) $ LM.PABMsg $ LM.SCoreMsg $ LM.FoundContract $ Just outputState

-- Get all installed contracts
runCliCommand t _ Config{dbConfig} _ ReportInstalledContracts = do
    connection <- App.dbConnect (LM.convertLog LM.PABMsg t) dbConfig
    fmap (either (error . show) id)
        $ Eventful.runEventfulStoreAction connection (LM.convertLog (LM.PABMsg . LM.SLoggerBridge) t)
        $ interpret (LM.handleLogMsgTrace t)
        $ do
            installedContracts <- Contract.getDefinitions @ContractExe
            traverse_ (logInfo @(LM.AppMsg ContractExe) . LM.InstalledContract . render . pretty) installedContracts
                where
                    render = renderStrict . layoutPretty defaultLayoutOptions

-- Get all active contracts
runCliCommand t _ Config{dbConfig} _ ReportActiveContracts = do
    connection <- App.dbConnect (LM.convertLog LM.PABMsg t) dbConfig
    fmap (either (error . show) id)
        $ Eventful.runEventfulStoreAction connection (LM.convertLog (LM.PABMsg . LM.SLoggerBridge) t)
        $ interpret (LM.handleLogMsgTrace t)
        $ do
            logInfo @(LM.AppMsg ContractExe) LM.ActiveContractsMsg
            instancesById <- Contract.getActiveContracts @ContractExe
            let idsByDefinition = Map.fromListWith (<>) $ fmap (\(inst, ContractActivationArgs{caID}) -> (caID, Set.singleton inst)) $ Map.toList instancesById
            traverse_ (\(e, s) -> logInfo @(LM.AppMsg ContractExe) $ LM.ContractInstances e (Set.toList s)) $ Map.toAscList idsByDefinition

-- Get history of a specific contract
runCliCommand t _ Config{dbConfig} _ (ReportContractHistory contractInstanceId) = do
    connection <- App.dbConnect (LM.convertLog LM.PABMsg t) dbConfig
    fmap (either (error . show) id)
        $ Eventful.runEventfulStoreAction connection (LM.convertLog (LM.PABMsg . LM.SLoggerBridge) t)
        $ interpret (LM.handleLogMsgTrace t)
        $ do
            logInfo @(LM.AppMsg ContractExe) LM.ContractHistoryMsg
            s <- Contract.getState @ContractExe contractInstanceId
            let PartiallyDecodedResponse{newState=State{record}} = Contract.serialisableState (Proxy @ContractExe) s
            traverse_ logStep (responses record)
                where
                    logStep response = logInfo @(LM.AppMsg ContractExe) $ LM.ContractHistoryItem contractInstanceId response

-- Generate PureScript bridge code
runCliCommand _ _ _ _ PSGenerator {_outputDir} =
    PSGenerator.generate _outputDir

-- Start the simulation web server & activate a contract.
runCliCommand _ _ _ _ StartSimulatorWebServer = do
    void $ Simulator.runSimulation $ do
        instanceId <- Simulator.activateContract (Wallet 1) Currency
        shutdown <- PABServer.startServerDebug
        _ <- liftIO getLine

        void $ do
            let endpointName = "Create native token"
                monetaryPolicy = SimpleMPS{tokenName="my token", amount = 10000}
            Simulator.callEndpointOnInstance instanceId endpointName monetaryPolicy
        _ <- liftIO getLine
        shutdown


-- Get default logging configuration
runCliCommand _ _ _ _ WriteDefaultConfig{_outputFile} =
    LM.defaultConfig >>= flip CM.exportConfiguration _outputFile

toPABMsg :: Trace m (LM.AppMsg ContractExe) -> Trace m LM.PABLogMsg
toPABMsg = LM.convertLog LM.PABMsg

toChainIndexLog :: Trace m (LM.AppMsg ContractExe) -> Trace m LM.ChainIndexServerMsg
toChainIndexLog = LM.convertLog $ LM.PABMsg . LM.SChainIndexServerMsg

toWalletLog :: Trace m (LM.AppMsg ContractExe) -> Trace m WalletMsg
toWalletLog = LM.convertLog $ LM.PABMsg . LM.SWalletMsg

toMetaDataLog :: Trace m (LM.AppMsg ContractExe) -> Trace m LM.MetadataLogMessage
toMetaDataLog = LM.convertLog $ LM.PABMsg . LM.SMetaDataLogMsg

toMockNodeServerLog :: Trace m (LM.AppMsg ContractExe) -> Trace m LM.MockServerLogMsg
toMockNodeServerLog = LM.convertLog $ LM.PABMsg . LM.SMockserverLogMsg
