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

import           Cardano.BM.Configuration                          (Configuration)
import qualified Cardano.BM.Configuration.Model                    as CM
import           Cardano.BM.Data.Trace                             (Trace)
import qualified Cardano.ChainIndex.Server                         as ChainIndex
import qualified Cardano.Metadata.Server                           as Metadata
import qualified Cardano.Node.Server                               as NodeServer
import qualified Cardano.Wallet.Server                             as WalletServer
import           Cardano.Wallet.Types
import           Control.Concurrent                                (threadDelay)
import           Control.Concurrent.Async                          (Async, async, waitAny)
import           Control.Concurrent.Availability                   (Availability, starting)
import           Control.Lens.Indexed                              (itraverse_)
import           Control.Monad                                     (forever, void)
import           Control.Monad.Freer                               (Eff, interpret, raise)
import           Control.Monad.Freer.Error                         (handleError)
import           Control.Monad.Freer.Extras.Log                    (LogMsg, logError, logInfo, mapLog)
import           Control.Monad.IO.Class                            (liftIO)
import           Data.Foldable                                     (traverse_)
import qualified Data.Map                                          as Map
import qualified Data.Set                                          as Set
import           Data.Text.Prettyprint.Doc                         (Pretty (..), defaultLayoutOptions, layoutPretty,
                                                                    pretty)
import           Data.Text.Prettyprint.Doc.Render.Text             (renderStrict)

import           Cardano.Node.Types                                (MockServerConfig (..), NodeUrl (..))
import           Data.Time.Units                                   (toMicroseconds)
import           Plutus.Contract.Effects.ExposeEndpoint   (EndpointDescription (..))
import           PlutusTx.Coordination.Contracts.Currency (SimpleMPS (..))
import qualified PSGenerator
import           Plutus.PAB.App                                    (runApp)
import qualified Plutus.PAB.App                                    as App
import qualified Plutus.PAB.Core                                   as Core
import qualified Plutus.PAB.Core.ContractInstance                  as Instance
import           Plutus.PAB.Effects.Contract.ContractTest          (TestContracts (Currency))
import           Plutus.PAB.Events.Contract                        (ContractInstanceId (..))
import           Plutus.PAB.Monitoring.MonadLoggerBridge           (TraceLoggerT, monadLoggerTracer)
import qualified Plutus.PAB.Monitoring.Monitoring                  as LM
import qualified Plutus.PAB.Simulator                              as Simulator
import           Plutus.PAB.Types                                  (Config (Config), PABError,
                                                                    RequestProcessingConfig (..), chainIndexConfig,
                                                                    metadataServerConfig, nodeServerConfig,
                                                                    requestProcessingConfig, walletServerConfig)
import qualified Plutus.PAB.Webserver.Server                       as PABServer
import           Wallet.Emulator.Wallet                            (Wallet (..))

-- | Interpret a 'Command' in 'Eff' using the provided tracer and configurations
--
runCliCommand ::
    Trace IO LM.AppMsg  -- ^ PAB Tracer logging instance
    -> Configuration -- ^ Monitoring configuration
    -> Config        -- ^ PAB Configuration
    -> Availability  -- ^ Token for signaling service availability
    -> Command
    -> IO ()

-- Run database migration
-- runCliCommand _ _ _ _ Migrate = raise App.migrate

-- Run mock wallet service
-- runCliCommand trace _ Config {..} serviceAvailability MockWallet =
--     liftIO $ WalletServer.main
--         (toWalletLog trace)
--         walletServerConfig
--         (NodeUrl $ mscBaseUrl nodeServerConfig)
--         (ChainIndex.ciBaseUrl chainIndexConfig)
--         serviceAvailability

-- Run mock node server
-- runCliCommand trace _ Config {nodeServerConfig} serviceAvailability MockNode =
--     liftIO $ NodeServer.main
--         (toMockNodeServerLog trace)
--         nodeServerConfig
--         serviceAvailability

-- Run mock metadata server
-- runCliCommand trace _ Config {metadataServerConfig} serviceAvailability Metadata =
--     liftIO $ Metadata.main
--         (toMetaDataLog trace)
--         metadataServerConfig
--         serviceAvailability

-- Run PAB webserver
-- runCliCommand trace logConfig config serviceAvailability PABWebserver =
--     raise $ PABServer.main
--         (toPABMsg trace)
--         logConfig
--         config
--         serviceAvailability

-- Fork a list of commands
-- runCliCommand trace logConfig config serviceAvailability (ForkCommands commands) =
--     void . liftIO $ do
--         threads <- traverse forkCommand commands
--         putStrLn "Started all commands."
--         waitAny threads
--   where
--     forkCommand ::  Command -> IO (Async ())
--     forkCommand subcommand = do
--       putStrLn $ "Starting: " <> show subcommand
--       -- see note [Use of iohk-monitoring in PAB]
--       let trace' = monadLoggerTracer trace
--       asyncId <- async . void . runApp (toPABMsg trace) logConfig config . LM.handleLogMsgTrace trace' . runCliCommand trace logConfig config serviceAvailability $ subcommand
--       putStrLn $ "Started: " <> show subcommand
--       starting serviceAvailability
--       pure asyncId

-- Run the chain-index service
-- runCliCommand t _ Config {nodeSer'verConfig, chainIndexConfig} serviceAvailability ChainIndex =
--     liftIO $ ChainIndex.main
--         (toChainIndexLog t)
--         chainIndexConfig
--         (mscSocketPath nodeServerConfig)
--         serviceAvailability'

-- Install a contract
-- runCliCommand _ _ _ _ (InstallContract path) =
--     interpret (mapLog LM.SCoreMsg)
--     $ Core.installContract (ContractExe path)

-- Activate a contract
-- runCliCommand _ _ _ _ (ActivateContract path) =
--     void
--     $ interpret (mapLog LM.SContractInstanceMsg)
--     $ interpret (mapLog LM.SCoreMsg)
--     $ Core.activateContract (ContractExe path)

-- Get the state of a contract
-- runCliCommand _ _ _ _ (ContractState uuid) =
--     interpret (mapLog LM.SCoreMsg)
--     $ Core.reportContractState @ContractExe (ContractInstanceId uuid)

-- Get all installed contracts
-- runCliCommand _ _ _ _ ReportInstalledContracts = do
--     logInfo LM.InstalledContractsMsg
--     traverse_ (logInfo . LM.InstalledContract . render . pretty) =<< Core.installedContracts @ContractExe
--         where
--             render = renderStrict . layoutPretty defaultLayoutOptions

-- Get all active contracts
-- runCliCommand _ _ _ _ ReportActiveContracts = do
--     logInfo LM.ActiveContractsMsg
--     instances <- Map.toAscList <$> Core.activeContracts @ContractExe
--     traverse_ (\(e, s) -> logInfo $ LM.ContractInstance e (Set.toList s)) instances

-- Get transaction history
-- runCliCommand _ _ _ _ ReportTxHistory = do
--     logInfo LM.TransactionHistoryMsg
--     traverse_ (logInfo . LM.TxHistoryItem) =<< Core.txHistory @ContractExe

-- Update a specific contract
-- runCliCommand _ _ _ _ (UpdateContract uuid endpoint payload) =
--     void
--     $ interpret (mapLog LM.SContractInstanceMsg)
--     $ Instance.callContractEndpoint @ContractExe (ContractInstanceId uuid) (getEndpointDescription endpoint) payload

-- Get history of a specific contract
-- runCliCommand _ _ _ _ (ReportContractHistory uuid) = do
--     logInfo LM.ContractHistoryMsg
--     contracts <- Core.activeContractHistory @ContractExe (ContractInstanceId uuid)
--     itraverse_ (\i -> logContract i) contracts
--     where
--       logContract index contract = logInfo $ LM.ContractHistoryItem index contract

-- Generate PureScript bridge code
runCliCommand _ _ _ _ PSGenerator {_outputDir} =
    liftIO $ PSGenerator.generate _outputDir

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
-- runCliCommand _ _ _ _ WriteDefaultConfig{_outputFile} =
    -- liftIO $ LM.defaultConfig >>= flip CM.exportConfiguration _outputFile

toPABMsg :: Trace m LM.AppMsg -> Trace m LM.PABLogMsg
toPABMsg = LM.convertLog LM.PABMsg

toChainIndexLog :: Trace m LM.AppMsg -> Trace m LM.ChainIndexServerMsg
toChainIndexLog = LM.convertLog $ LM.PABMsg . LM.SChainIndexServerMsg

toWalletLog :: Trace m LM.AppMsg -> Trace m WalletMsg
toWalletLog = LM.convertLog $ LM.PABMsg . LM.SWalletMsg

toMetaDataLog :: Trace m LM.AppMsg -> Trace m LM.MetadataLogMessage
toMetaDataLog = LM.convertLog $ LM.PABMsg . LM.SMetaDataLogMsg

toMockNodeServerLog :: Trace m LM.AppMsg -> Trace m LM.MockServerLogMsg
toMockNodeServerLog = LM.convertLog $ LM.PABMsg . LM.SMockserverLogMsg
