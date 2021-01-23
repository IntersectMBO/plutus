{-# LANGUAGE ApplicativeDo         #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE DeriveGeneric         #-}
{-# LANGUAGE DerivingVia           #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns        #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeOperators         #-}

module Main
    ( main
    ) where

import qualified Cardano.BM.Backend.EKGView
import           Cardano.BM.Configuration                        (Configuration)
import qualified Cardano.BM.Configuration.Model                  as CM
import           Cardano.BM.Data.Severity                        (Severity (..))
import           Cardano.BM.Data.Trace                           (Trace)
import           Cardano.BM.Plugin                               (loadPlugin)
import           Cardano.BM.Setup                                (setupTrace_)
import qualified Cardano.ChainIndex.Server                       as ChainIndex
import qualified Cardano.Metadata.Server                         as Metadata
import qualified Cardano.Node.Server                             as NodeServer
import qualified Cardano.SigningProcess.Server                   as SigningProcess
import qualified Cardano.Wallet.Server                           as WalletServer
import           Control.Concurrent                              (threadDelay)
import           Control.Concurrent.Async                        (Async, async, waitAny)
import           Control.Concurrent.Availability                 (Availability, newToken, starting)
import           Control.Lens.Indexed                            (itraverse_)
import           Control.Monad                                   (forever, void, when)
import           Control.Monad.Freer                             (Eff, raise)
import           Control.Monad.Freer.Error                       (handleError)
import           Control.Monad.Freer.Extra.Log                   (LogMsg, logInfo)
import           Control.Monad.Freer.Log                         (logError)
import           Control.Monad.IO.Class                          (liftIO)
import           Control.Monad.Logger                            (runStdoutLoggingT)
import qualified Data.Aeson                                      as JSON
import           Data.Bifunctor                                  (Bifunctor (..))
import qualified Data.ByteString.Lazy.Char8                      as BS8
import           Data.Foldable                                   (for_, traverse_)
import           Data.Functor.Contravariant                      (Contravariant (..))
import qualified Data.Map                                        as Map
import qualified Data.Set                                        as Set
import qualified Data.Text                                       as Text
import           GHC.Generics                                    (Generic)
import           Plutus.PAB.MonadLoggerBridge                    (TraceLoggerT (..))
import           Plutus.PAB.Monitoring                           (defaultConfig, handleLogMsgTrace, loadConfig)

import           Data.Text.Prettyprint.Doc                       (Pretty (..), pretty)
import           Data.Time.Units                                 (toMicroseconds)
import           Data.UUID                                       (UUID)
import           Data.Yaml                                       (decodeFileThrow)
import           Git                                             (gitRev)
import           Language.Plutus.Contract.Effects.ExposeEndpoint (EndpointDescription (..))
import           Options.Applicative                             (CommandFields, Mod, Parser, argument, auto, command,
                                                                  customExecParser, disambiguate, eitherReader, flag,
                                                                  fullDesc, help, helper, idm, info, infoOption, long,
                                                                  metavar, option, prefs, progDesc, short,
                                                                  showHelpOnEmpty, showHelpOnError, str, strArgument,
                                                                  strOption, subparser, value)
import qualified PSGenerator
import           Plutus.PAB.App                                  (AppBackend, monadLoggerTracer, runApp)
import qualified Plutus.PAB.App                                  as App
import qualified Plutus.PAB.Core                                 as Core
import qualified Plutus.PAB.Core.ContractInstance                as Instance
import           Plutus.PAB.Events.Contract                      (ContractInstanceId (..))
import           Plutus.PAB.PABLogMsg                            (AppMsg (..), ContractExeLogMsg (..), PABLogMsg)
import           Plutus.PAB.Types                                (Config (Config), ContractExe (..), PABError,
                                                                  RequestProcessingConfig (..), chainIndexConfig,
                                                                  metadataServerConfig, nodeServerConfig,
                                                                  requestProcessingConfig, signingProcessConfig,
                                                                  walletServerConfig)
import           Plutus.PAB.Utils                                (logErrorS, render)
import qualified Plutus.PAB.Webserver.Server                     as PABServer
import           System.Exit                                     (ExitCode (ExitFailure), exitSuccess, exitWith)

data Command
    = Migrate
    | MockNode
    | MockWallet
    | ChainIndex
    | Metadata
    | ForkCommands [Command]
    | SigningProcess
    | InstallContract FilePath
    | ActivateContract FilePath
    | ContractState UUID
    | UpdateContract UUID EndpointDescription JSON.Value
    | ReportContractHistory UUID
    | ReportInstalledContracts
    | ReportActiveContracts
    | ProcessContractInbox UUID
    | ProcessAllContractOutboxes
    | ReportTxHistory
    | PABWebserver
    | PSGenerator
          { _outputDir :: !FilePath
          }
    | WriteDefaultConfig
          { _outputFile :: !FilePath
          }
    deriving stock (Show, Eq, Generic)
    deriving anyclass JSON.ToJSON

versionOption :: Parser (a -> a)
versionOption =
    infoOption
        (Text.unpack gitRev)
        (long "version" <> help "Show the version")

logLevelFlag :: Parser (Maybe Severity)
logLevelFlag =
    flag
        Nothing
        (Just Debug)
        (short 'v' <> long "verbose" <> help "Enable debugging output.")

data EKGServer = YesEKGServer | NoEKGServer
    deriving (Eq, Ord, Show)

ekgFlag :: Parser EKGServer
ekgFlag =
    flag
        NoEKGServer
        YesEKGServer
        (short 'e' <> long "ekg" <> help "Enable the EKG server")

commandLineParser :: Parser (Maybe Severity, FilePath, Maybe FilePath, EKGServer, Command)
commandLineParser =
        (,,,,) <$> logLevelFlag
               <*> configFileParser
               <*> logConfigFileParser
               <*> ekgFlag
               <*> commandParser

configFileParser :: Parser FilePath
configFileParser =
    option
        str
        (long "config" <>
         metavar "CONFIG_FILE" <>
         help "Config file location." <> value "plutus-pab.yaml")

logConfigFileParser :: Parser (Maybe FilePath)
logConfigFileParser =
    option
        (Just <$> str)
        (long "log-config" <>
         metavar "LOG_CONFIG_FILE" <>
         help "Logging config file location." <> value Nothing)

commandParser :: Parser Command
commandParser =
    subparser $
    mconcat
        [ migrationParser
        , allServersParser
        , clientServicesParser
        , mockWalletParser
        , pabWebserverParser
        , psGeneratorCommandParser
        , mockNodeParser
        , chainIndexParser
        , metadataParser
        , signingProcessParser
        , reportTxHistoryParser
        , defaultConfigParser
        , command
              "contracts"
              (info
                   (subparser
                        (mconcat
                             [ installContractParser
                             , reportInstalledContractsParser
                             , activateContractParser
                             , reportActiveContractsParser
                             , updateContractParser
                             , contractStateParser
                             , reportContractHistoryParser
                             , processAllContractInboxesParser
                             , processAllContractOutboxesParser
                             ]))
                   (fullDesc <> progDesc "Manage your smart contracts."))
        ]

defaultConfigParser :: Mod CommandFields Command
defaultConfigParser =
    command "default-logging-config" $
    flip info (fullDesc <> progDesc "Write the default logging configuration YAML to a file") $ do
        _outputFile <-
            argument
                str
                (metavar "OUTPUT_FILE" <>
                 help "Output file to write logging config YAML to.")
        pure WriteDefaultConfig {_outputFile}

psGeneratorCommandParser :: Mod CommandFields Command
psGeneratorCommandParser =
    command "psgenerator" $
    flip info (fullDesc <> progDesc "Generate the frontend's PureScript files.") $ do
        _outputDir <-
            argument
                str
                (metavar "OUTPUT_DIR" <>
                 help "Output directory to write PureScript files to.")
        pure PSGenerator {_outputDir}

migrationParser :: Mod CommandFields Command
migrationParser =
    command "migrate" $
    info
        (pure Migrate)
        (fullDesc <> progDesc "Update the database with the latest schema.")

mockNodeParser :: Mod CommandFields Command
mockNodeParser =
    command "node-server" $
    info
        (pure MockNode)
        (fullDesc <>
         progDesc "Run a mock version of the Cardano node API server.")

mockWalletParser :: Mod CommandFields Command
mockWalletParser =
    command "wallet-server" $
    info
        (pure MockWallet)
        (fullDesc <>
         progDesc "Run a mock version of the Cardano wallet API server.")

chainIndexParser :: Mod CommandFields Command
chainIndexParser =
    command "chain-index" $
    info (pure ChainIndex) (fullDesc <> progDesc "Run the chain index.")

metadataParser :: Mod CommandFields Command
metadataParser =
    command "metadata-server" $
    info (pure Metadata) (fullDesc <> progDesc "Run the Cardano metadata API server.")

allServersParser :: Mod CommandFields Command
allServersParser =
    command "all-servers" $
    info
        (pure
             (ForkCommands
                  [ MockNode
                  , ChainIndex
                  , Metadata
                  , MockWallet
                  , PABWebserver
                  , SigningProcess
                  , ProcessAllContractOutboxes
                  ]))
        (fullDesc <> progDesc "Run all the mock servers needed.")

clientServicesParser :: Mod CommandFields Command
clientServicesParser =
    command "client-services" $
    info
        (pure
             (ForkCommands
                  [ ChainIndex
                  , Metadata
                  , MockWallet
                  , PABWebserver
                  , SigningProcess
                  , ProcessAllContractOutboxes
                  ]))
        (fullDesc <> progDesc "Run the client services (all services except the mock node).")

signingProcessParser :: Mod CommandFields Command
signingProcessParser =
    command "signing-process" $
    info (pure SigningProcess) (fullDesc <> progDesc "Run the signing process.")

activateContractParser :: Mod CommandFields Command
activateContractParser =
    command "activate" $
    info
        (ActivateContract <$>
         strOption
             (short 'p' <>
              long "path" <>
              help
                  "Name of the contract. (See 'installed-contracts' for a list.)"))
        (fullDesc <> progDesc "Activate a smart contract.")

installContractParser :: Mod CommandFields Command
installContractParser =
    command "install" $
    info
        (InstallContract <$>
         strOption
             (short 'p' <>
              long "path" <> help "Path to the executable contract."))
        (fullDesc <> progDesc "Install a new smart contract.")

contractStateParser :: Mod CommandFields Command
contractStateParser =
    command "state" $
    info
        (ContractState <$> contractIdParser)
        (fullDesc <> progDesc "Show the current state of a contract.")

contractIdParser :: Parser UUID
contractIdParser =
    argument
        auto
        (help "ID of the contract. (See 'active-contracts' for a list.)")

reportInstalledContractsParser :: Mod CommandFields Command
reportInstalledContractsParser =
    command "installed" $
    info
        (pure ReportInstalledContracts)
        (fullDesc <> progDesc "Show all installed contracts.")

reportActiveContractsParser :: Mod CommandFields Command
reportActiveContractsParser =
    command "active" $
    info
        (pure ReportActiveContracts)
        (fullDesc <> progDesc "Show all active contracts.")

reportTxHistoryParser :: Mod CommandFields Command
reportTxHistoryParser =
    command "local-chain" $
    info
        (pure ReportTxHistory)
        (fullDesc <> progDesc "Show all submitted transactions.")

pabWebserverParser :: Mod CommandFields Command
pabWebserverParser =
    command "webserver" $
    info
        (pure PABWebserver)
        (fullDesc <> progDesc "Start the PAB backend webserver.")

updateContractParser :: Mod CommandFields Command
updateContractParser =
    command "update" $
    info
        (UpdateContract <$> contractIdParser <*>
         strArgument (help "Endpoint name.") <*>
         argument
             (eitherReader (JSON.eitherDecode . BS8.pack))
             (help "JSON Payload."))
        (fullDesc <> progDesc "Update a smart contract.")

processAllContractInboxesParser :: Mod CommandFields Command
processAllContractInboxesParser =
    command "process-inbox" $
    info
        (ProcessContractInbox <$> contractIdParser)
        (fullDesc <> progDesc "Process the inbox of the contract instance.")

processAllContractOutboxesParser :: Mod CommandFields Command
processAllContractOutboxesParser =
    command "process-outboxes" $
    info
        (pure ProcessAllContractOutboxes)
        (fullDesc <> progDesc "Process all contract outboxes.")

reportContractHistoryParser :: Mod CommandFields Command
reportContractHistoryParser =
    command "history" $
    info
        (ReportContractHistory <$> contractIdParser)
        (fullDesc <> progDesc "Show the state history of a smart contract.")

{- Note [Use of iohk-monitoring in PAB]

We use the 'iohk-monitoring' package to process the log messages that come
out of the 'Control.Monad.Freer.Log' effects. We create a top-level 'Tracer'
value that we pass to 'Plutus.PAB.Monitoring.handleLogMsgTrace', which
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
provided by 'Plutus.PAB.MonadLoggerBridge.TraceLoggerT', which translates
'MonadLogger' calls to 'Tracer' calls. This is why the base monad of the
effects stack in 'runCliCommand' is 'TraceLoggerT IO' instead of just 'IO'.

We have to use 'natTracer' in some places to turn 'Trace IO a' into
'Trace (TraceLoggerT IO) a'.

[1] https://hackage.haskell.org/package/freer-simple-1.2.1.1/docs/Control-Monad-Freer.html#t:Eff

-}

------------------------------------------------------------
-- | Translate the command line configuation into the actual code to be run.
--
runCliCommand :: Trace IO AppMsg -> Configuration -> Config ->  Availability -> Command -> Eff (LogMsg AppMsg ': AppBackend (TraceLoggerT IO)) ()
runCliCommand _ _ _ _ Migrate = raise App.migrate
runCliCommand _ _ Config {walletServerConfig, nodeServerConfig, chainIndexConfig} serviceAvailability MockWallet =
    WalletServer.main
        walletServerConfig
        (NodeServer.mscBaseUrl nodeServerConfig)
        (ChainIndex.ciBaseUrl chainIndexConfig)
        serviceAvailability
runCliCommand _ _ Config {nodeServerConfig} serviceAvailability MockNode =
    NodeServer.main nodeServerConfig serviceAvailability
runCliCommand _ _ Config {metadataServerConfig} serviceAvailability Metadata = raise $ Metadata.main metadataServerConfig serviceAvailability
runCliCommand trace logConfig config serviceAvailability PABWebserver = raise $ PABServer.main (mapPABMsg trace) logConfig config serviceAvailability
runCliCommand trace logConfig config serviceAvailability (ForkCommands commands) =
    void . liftIO $ do
        threads <- traverse forkCommand commands
        putStrLn "Started all commands."
        waitAny threads
  where

    forkCommand ::  Command -> IO (Async ())
    forkCommand subcommand = do
      putStrLn $ "Starting: " <> show subcommand
      -- see note [Use of iohk-monitoring in PAB]
      let trace' = monadLoggerTracer trace
      asyncId <- async . void . runApp (mapPABMsg trace) logConfig config . handleLogMsgTrace trace' . runCliCommand trace logConfig config serviceAvailability $ subcommand
      putStrLn $ "Started: " <> show subcommand
      starting serviceAvailability
      pure asyncId
runCliCommand _ _ Config {nodeServerConfig, chainIndexConfig} serviceAvailability ChainIndex =
    ChainIndex.main chainIndexConfig (NodeServer.mscBaseUrl nodeServerConfig) serviceAvailability
runCliCommand _ _ Config {signingProcessConfig} serviceAvailability SigningProcess =
    SigningProcess.main signingProcessConfig serviceAvailability
runCliCommand _ _ _ _ (InstallContract path) = Core.installContract (ContractExe path)
runCliCommand _ _ _ _ (ActivateContract path) = void $ Core.activateContract (ContractExe path)
runCliCommand _ _ _ _ (ContractState uuid) = Core.reportContractState @ContractExe (ContractInstanceId uuid)
runCliCommand _ _ _ _ ReportInstalledContracts = do
    logInfo InstalledContractsMsg
    traverse_ (logInfo . InstalledContract . render . pretty) =<< Core.installedContracts @ContractExe
runCliCommand _ _ _ _ ReportActiveContracts = do
    logInfo ActiveContractsMsg
    instances <- Map.toAscList <$> Core.activeContracts @ContractExe
    traverse_ (\(e, s) -> logInfo $ ContractInstance e (Set.toList s)) instances
runCliCommand _ _ _ _ ReportTxHistory = do
    logInfo TransactionHistoryMsg
    traverse_ (logInfo . TxHistoryItem) =<< Core.txHistory @ContractExe
runCliCommand _ _ _ _ (UpdateContract uuid endpoint payload) =
    void $ Instance.callContractEndpoint @ContractExe (ContractInstanceId uuid) (getEndpointDescription endpoint) payload
runCliCommand _ _ _ _ (ReportContractHistory uuid) = do
    logInfo ContractHistoryMsg
    contracts <- Core.activeContractHistory @ContractExe (ContractInstanceId uuid)
    itraverse_ (\i -> logContract i) contracts
    where
      logContract index contract = logInfo $ ContractHistoryItem index contract
runCliCommand _ _ _ _ (ProcessContractInbox uuid) = do
    logInfo ProcessInboxMsg
    Core.processContractInbox @ContractExe (ContractInstanceId uuid)
runCliCommand _ _ Config{requestProcessingConfig} _ ProcessAllContractOutboxes = do
    let RequestProcessingConfig{requestProcessingInterval} = requestProcessingConfig
    logInfo $ ProcessAllOutboxesMsg requestProcessingInterval
    forever $ do
        _ <- liftIO . threadDelay . fromIntegral $ toMicroseconds requestProcessingInterval
        handleError @PABError (Core.processAllContractOutboxes @ContractExe Instance.defaultMaxIterations) (logError . ContractExePABError)
runCliCommand _ _ _ _ PSGenerator {_outputDir} =
    liftIO $ PSGenerator.generate _outputDir
runCliCommand _ _ _ _ WriteDefaultConfig{_outputFile} =
    liftIO $ defaultConfig >>= flip CM.exportConfiguration _outputFile

main :: IO ()
main = do
    (minLogLevel, configPath, logConfigPath, ekg, cmd) <-
        customExecParser
            (prefs $ disambiguate <> showHelpOnEmpty <> showHelpOnError)
            (info (helper <*> versionOption <*> commandLineParser) idm)
    config <- liftIO $ decodeFileThrow configPath

    logConfig <- maybe defaultConfig loadConfig logConfigPath
    for_ minLogLevel $ \ll -> CM.setMinSeverity logConfig ll
    (trace :: Trace IO AppMsg, switchboard) <- setupTrace_ logConfig pabComponentName

    -- 'TracerLoggerT IO' has instances for 'MonadLogger' and 'MonadUnliftIO'.
    -- see note [Use of iohk-monitoring in PAB]
    let trace' = monadLoggerTracer trace

    -- enable EKG backend
    when (ekg == YesEKGServer) $
        Cardano.BM.Backend.EKGView.plugin logConfig trace switchboard >>= loadPlugin switchboard

    serviceAvailability <- newToken
    result <-
        runApp (mapPABMsg trace) logConfig config
            $ handleLogMsgTrace trace'
            $ runCliCommand trace logConfig config serviceAvailability cmd
    case result of
        Left err -> do
            runStdoutLoggingT $ logErrorS err
            exitWith (ExitFailure 1)
        Right _ -> exitSuccess

mapPABMsg :: Trace m AppMsg -> Trace m PABLogMsg
mapPABMsg = contramap (second (fmap PABMsg))

pabComponentName :: Text.Text
pabComponentName = "pab"
