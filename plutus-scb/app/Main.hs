{-# LANGUAGE ApplicativeDo       #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE NamedFieldPuns      #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}

module Main
    ( main
    ) where

import qualified Cardano.ChainIndex.Server     as ChainIndex
import qualified Cardano.Node.Server           as NodeServer
import qualified Cardano.SigningProcess.Server as SigningProcess
import qualified Cardano.Wallet.Server         as WalletServer
import           Control.Concurrent.Async      (Async, async, waitAny)
import           Control.Lens.Indexed          (itraverse_)
import           Control.Monad                 (void)
import           Control.Monad.Freer.Extra.Log (logInfo)
import           Control.Monad.IO.Class        (liftIO)
import           Control.Monad.Logger          (LogLevel (LevelDebug, LevelInfo), filterLogger, runStdoutLoggingT)
import qualified Data.Aeson                    as JSON
import qualified Data.ByteString.Lazy.Char8    as BS8
import           Data.Foldable                 (traverse_)
import           Data.Text                     (Text)
import qualified Data.Text                     as Text
import           Data.Text.Prettyprint.Doc     (parens, pretty, (<+>))
import           Data.UUID                     (UUID)
import           Data.Yaml                     (decodeFileThrow)
import           Git                           (gitRev)
import           Options.Applicative           (CommandFields, Mod, Parser, argument, auto, command, customExecParser,
                                                disambiguate, eitherReader, flag, fullDesc, help, helper, idm, info,
                                                infoOption, long, metavar, option, optional, prefs, progDesc, short,
                                                showHelpOnEmpty, showHelpOnError, str, strArgument, strOption,
                                                subparser, value)
import           Plutus.SCB.App                (App, runApp)
import qualified Plutus.SCB.App                as App
import qualified Plutus.SCB.Core               as Core
import           Plutus.SCB.Types              (Config (Config), ContractExe (..), chainIndexConfig, nodeServerConfig,
                                                signingProcessConfig, walletServerConfig)
import           Plutus.SCB.Utils              (logErrorS, render)
import qualified Plutus.SCB.Webserver.Server   as SCBServer
import qualified PSGenerator
import           System.Exit                   (ExitCode (ExitFailure), exitSuccess, exitWith)
import qualified System.Remote.Monitoring      as EKG

data Command
    = Migrate
    | MockNode
    | MockWallet
    | ChainIndex
    | ForkCommands [Command]
    | SigningProcess
    | InstallContract FilePath
    | ActivateContract FilePath
    | ContractStatus UUID
    | UpdateContract UUID Text JSON.Value
    | ReportContractHistory UUID
    | ReportInstalledContracts
    | ReportActiveContracts
    | ReportTxHistory
    | SCBWebserver
    | PSGenerator
          { _outputDir :: !FilePath
          }
    deriving (Show, Eq)

versionOption :: Parser (a -> a)
versionOption =
    infoOption
        (Text.unpack gitRev)
        (long "version" <> help "Show the version")

logLevelFlag :: Parser LogLevel
logLevelFlag =
    flag
        LevelInfo
        LevelDebug
        (short 'v' <> long "verbose" <> help "Enable debugging output.")

commandLineParser :: Parser (Maybe Int, LogLevel, FilePath, Command)
commandLineParser =
    (,,,) <$> optional ekgPortParser <*> logLevelFlag <*> configFileParser <*>
    commandParser

ekgPortParser :: Parser Int
ekgPortParser =
    option
        auto
        (long "monitoring-port" <>
         short 'p' <> metavar "PORT" <> help "Open an EKG server on PORT")

configFileParser :: Parser FilePath
configFileParser =
    option
        str
        (long "config" <>
         metavar "CONFIG_FILE" <>
         help "Config file location." <> value "plutus-scb.yaml")

commandParser :: Parser Command
commandParser =
    subparser $
    mconcat
        [ migrationParser
        , allServersParser
        , mockWalletParser
        , scbWebserverParser
        , psGeneratorCommandParser
        , mockNodeParser
        , chainIndexParser
        , signingProcessParser
        , command
              "contracts"
              (info
                   (subparser
                        (mconcat
                             [ installContractParser
                             , reportInstalledContractsParser
                             , activateContractParser
                             , reportActiveContractsParser
                             , reportTxHistoryParser
                             , updateContractParser
                             , contractStatusParser
                             , reportContractHistoryParser
                             ]))
                   (fullDesc <> progDesc "Manage your smart contracts."))
        ]

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

allServersParser :: Mod CommandFields Command
allServersParser =
    command "all-servers" $
    info
        (pure
             (ForkCommands
                  [ MockNode
                  , MockWallet
                  , ChainIndex
                  , SigningProcess
                  , SCBWebserver
                  ]))
        (fullDesc <> progDesc "Run all the mock servers needed.")

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

contractStatusParser :: Mod CommandFields Command
contractStatusParser =
    command "status" $
    info
        (ContractStatus <$> contractIdParser)
        (fullDesc <> progDesc "Show the current status of a contract.")

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
    command "tx" $
    info
        (pure ReportTxHistory)
        (fullDesc <> progDesc "Show all submitted transactions.")

scbWebserverParser :: Mod CommandFields Command
scbWebserverParser =
    command "webserver" $
    info
        (pure SCBWebserver)
        (fullDesc <> progDesc "Start the SCB backend webserver.")

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

reportContractHistoryParser :: Mod CommandFields Command
reportContractHistoryParser =
    command "history" $
    info
        (ReportContractHistory <$> contractIdParser)
        (fullDesc <> progDesc "Show the state history of a smart contract.")

------------------------------------------------------------
runCliCommand :: LogLevel -> Config -> Command -> App ()
runCliCommand _ _ Migrate = App.migrate
runCliCommand _ Config {walletServerConfig, nodeServerConfig, chainIndexConfig} MockWallet =
    WalletServer.main
        walletServerConfig
        (NodeServer.mscBaseUrl nodeServerConfig)
        (ChainIndex.ciBaseUrl chainIndexConfig)
runCliCommand _ Config {nodeServerConfig} MockNode =
    NodeServer.main nodeServerConfig
runCliCommand _ config SCBWebserver = SCBServer.main config
runCliCommand minLogLevel config (ForkCommands commands) =
    void . liftIO $ do
        threads <- traverse forkCommand commands
        waitAny threads
  where
    forkCommand ::  Command -> IO (Async ())
    forkCommand = async . void . runApp minLogLevel config . runCliCommand minLogLevel config
runCliCommand _ Config {nodeServerConfig, chainIndexConfig} ChainIndex =
    ChainIndex.main chainIndexConfig (NodeServer.mscBaseUrl nodeServerConfig)
runCliCommand _ Config {signingProcessConfig} SigningProcess =
    SigningProcess.main signingProcessConfig
runCliCommand _ _ (InstallContract path) = Core.installContract (ContractExe path)
runCliCommand _ _ (ActivateContract path) = void $ Core.activateContract (ContractExe path)
runCliCommand _ _ (ContractStatus uuid) = Core.reportContractStatus @ContractExe uuid
runCliCommand _ _ ReportInstalledContracts = do
    logInfo "Installed Contracts"
    traverse_ (logInfo . render . pretty) =<< Core.installedContracts @ContractExe
runCliCommand _ _ ReportActiveContracts = do
    logInfo "Active Contracts"
    traverse_ (logInfo . render . pretty) =<< Core.activeContracts @ContractExe
runCliCommand _ _ ReportTxHistory = do
    logInfo "Transaction History"
    traverse_ (logInfo . render . pretty) =<< Core.txHistory @ContractExe
runCliCommand _ _ (UpdateContract uuid endpoint payload) =
    Core.updateContract @ContractExe uuid endpoint payload
runCliCommand _ _ (ReportContractHistory uuid) = do
    logInfo "Contract History"
    itraverse_
        (\index contract ->
             logInfo $ render (parens (pretty index) <+> pretty contract)) =<<
        Core.activeContractHistory @ContractExe uuid
runCliCommand _ _ PSGenerator {_outputDir} =
    liftIO $ PSGenerator.generate _outputDir

main :: IO ()
main = do
    (ekgPort, minLogLevel, configPath, cmd) <-
        customExecParser
            (prefs $ disambiguate <> showHelpOnEmpty <> showHelpOnError)
            (info (helper <*> versionOption <*> commandLineParser) idm)
    config <- liftIO $ decodeFileThrow configPath
    traverse_ (EKG.forkServer "localhost") ekgPort
    result <-
        runApp minLogLevel config $ do
            logInfo $ "Running: " <> Text.pack (show cmd)
            runCliCommand minLogLevel config cmd
    case result of
        Left err -> do
            runStdoutLoggingT $ filterLogger (\_ logLevel -> logLevel >= minLogLevel) $ logErrorS err
            exitWith (ExitFailure 1)
        Right _ -> exitSuccess
