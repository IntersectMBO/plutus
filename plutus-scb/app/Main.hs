{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE NamedFieldPuns      #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}

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
import           Control.Monad.Logger          (runStdoutLoggingT)
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
                                                disambiguate, eitherReader, fullDesc, help, helper, idm, info,
                                                infoOption, long, metavar, option, optional, prefs, progDesc, short,
                                                showHelpOnEmpty, showHelpOnError, str, strArgument, strOption,
                                                subparser, value, (<|>))
import           Plutus.SCB.App                (App, runApp)
import qualified Plutus.SCB.App                as App
import qualified Plutus.SCB.Core               as Core
import           Plutus.SCB.Types              (Config (Config), chainIndexConfig, nodeServerConfig,
                                                signingProcessConfig, walletServerConfig)
import           Plutus.SCB.Utils              (logErrorS, render)
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
    deriving (Show, Eq)

versionOption :: Parser (a -> a)
versionOption =
    infoOption
        (Text.unpack gitRev)
        (short 'v' <> long "version" <> help "Show the version")

commandLineParser :: Parser (Maybe Int, FilePath, Command)
commandLineParser =
    (,,) <$> optional ekgPortParser <*> configFileParser <*> commandParser

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
    subparser
        (mconcat
             [ migrationParser
             , allServersParser
             , mockWalletParser
             , mockNodeParser
             , chainIndexParser
             , signingProcessParser
             ]) <|>
    subparser
        (command
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
                  (fullDesc <> progDesc "Manage your smart contracts.")))

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
        (pure (ForkCommands [MockNode, MockWallet, ChainIndex, SigningProcess]))
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
runCliCommand :: Config -> Command -> App ()
runCliCommand _ Migrate = App.migrate
runCliCommand Config {walletServerConfig, nodeServerConfig, chainIndexConfig} MockWallet =
    WalletServer.main
        walletServerConfig
        (NodeServer.mscBaseUrl nodeServerConfig)
        (ChainIndex.ciBaseUrl chainIndexConfig)
runCliCommand Config {nodeServerConfig} MockNode =
    NodeServer.main nodeServerConfig
runCliCommand config (ForkCommands commands) =
    void . liftIO $ do
        threads <- traverse forkCommand commands
        waitAny threads
  where
    forkCommand :: Command -> IO (Async ())
    forkCommand = async . void . runApp config . runCliCommand config
runCliCommand Config {nodeServerConfig, chainIndexConfig} ChainIndex =
    ChainIndex.main chainIndexConfig (NodeServer.mscBaseUrl nodeServerConfig)
runCliCommand Config {signingProcessConfig} SigningProcess =
    SigningProcess.main signingProcessConfig
runCliCommand _ (InstallContract path) = Core.installContract path
runCliCommand _ (ActivateContract path) = void $ Core.activateContract path
runCliCommand _ (ContractStatus uuid) = Core.reportContractStatus uuid
runCliCommand _ ReportInstalledContracts = do
    logInfo "Installed Contracts"
    traverse_ (logInfo . render . pretty) =<< Core.installedContracts
runCliCommand _ ReportActiveContracts = do
    logInfo "Active Contracts"
    traverse_ (logInfo . render . pretty) =<< Core.activeContracts
runCliCommand _ ReportTxHistory = do
    logInfo "Transaction History"
    traverse_ (logInfo . render . pretty) =<< Core.txHistory
runCliCommand _ (UpdateContract uuid endpoint payload) =
    Core.updateContract uuid endpoint payload
runCliCommand _ (ReportContractHistory uuid) = do
    logInfo "Contract History"
    itraverse_
        (\index contract ->
             logInfo $ render (parens (pretty index) <+> pretty contract)) =<<
        Core.activeContractHistory uuid

main :: IO ()
main = do
    (ekgPort, configPath, cmd) <-
        customExecParser
            (prefs $ disambiguate <> showHelpOnEmpty <> showHelpOnError)
            (info (helper <*> versionOption <*> commandLineParser) idm)
    config <- liftIO $ decodeFileThrow configPath
    traverse_ (EKG.forkServer "localhost") ekgPort
    result <-
        runApp config $ do
            logInfo $ "Running: " <> Text.pack (show cmd)
            runCliCommand config cmd
    case result of
        Left err -> do
            runStdoutLoggingT $ logErrorS err
            exitWith (ExitFailure 1)
        Right _ -> exitSuccess
