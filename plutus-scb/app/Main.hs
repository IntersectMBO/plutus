{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE OverloadedStrings #-}

module Main
    ( main
    ) where

import qualified Cardano.Node.Client             as NodeClient
import qualified Cardano.Node.MockServer         as NodeServer
import qualified Cardano.Wallet.Client           as WalletClient
import qualified Cardano.Wallet.MockServer       as WalletServer
import           Control.Lens.Indexed            (itraverse_)
import           Control.Monad.IO.Class          (liftIO)
import           Control.Monad.Logger            (logInfoN, runStdoutLoggingT)
import qualified Data.Aeson                      as JSON
import qualified Data.ByteString.Lazy.Char8      as BS8
import           Data.Foldable                   (traverse_)
import           Data.Text                       (Text)
import qualified Data.Text                       as Text
import           Data.UUID                       (UUID)
import           Data.Yaml                       (decodeFileThrow)
import           Git                             (gitRev)
import           Options.Applicative             (CommandFields, Mod, Parser, argument, auto, command, customExecParser,
                                                  disambiguate, eitherReader, fullDesc, help, helper, idm, info,
                                                  infoOption, long, metavar, option, optional, prefs, progDesc, short,
                                                  showHelpOnEmpty, showHelpOnError, str, strArgument, strOption,
                                                  subparser, value, (<|>))
import           Options.Applicative.Help.Pretty (int, parens, pretty, (<+>))
import           Plutus.SCB.App                  (App, runApp)
import qualified Plutus.SCB.App                  as App
import qualified Plutus.SCB.Core                 as Core
import           Plutus.SCB.Utils                (logErrorS, render)
import           System.Exit                     (ExitCode (ExitFailure, ExitSuccess), exitWith)
import qualified System.Remote.Monitoring        as EKG

data Command
    = Migrate
    | MockNode
    | MockWallet
    | WalletClient
    | NodeClient
    | InstallContract FilePath
    | ActivateContract FilePath
    | ContractStatus UUID
    | UpdateContract UUID Text JSON.Value
    | ReportContractHistory UUID
    | ReportInstalledContracts
    | ReportActiveContracts
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
             , mockWalletParser
             , walletClientParser
             , mockNodeParser
             , nodeClientParser
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

nodeClientParser :: Mod CommandFields Command
nodeClientParser =
    command "node-client" $
    info
        (pure NodeClient)
        (fullDesc <> progDesc "Run a basic query against the Cardano node API.")

mockWalletParser :: Mod CommandFields Command
mockWalletParser =
    command "wallet-server" $
    info
        (pure MockWallet)
        (fullDesc <>
         progDesc "Run a mock version of the Cardano wallet API server.")

walletClientParser :: Mod CommandFields Command
walletClientParser =
    command "wallet-client" $
    info
        (pure WalletClient)
        (fullDesc <>
         progDesc "Run a basic query against the Cardano wallet API.")

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
runCliCommand :: Command -> App ()
runCliCommand Migrate = App.migrate
runCliCommand MockWallet = WalletServer.main
runCliCommand MockNode = NodeServer.main NodeServer.defaultConfig
runCliCommand WalletClient = liftIO WalletClient.main
runCliCommand NodeClient = liftIO NodeClient.main
runCliCommand (InstallContract path) = Core.installContract path
runCliCommand (ActivateContract path) = Core.activateContract path
runCliCommand (ContractStatus uuid) = Core.reportContractStatus uuid
runCliCommand ReportInstalledContracts = do
    logInfoN "Installed Contracts"
    traverse_ (logInfoN . render) =<< Core.installedContracts
    pure ()
runCliCommand ReportActiveContracts = do
    logInfoN "Active Contracts"
    traverse_ (logInfoN . render) =<< Core.activeContracts
    pure ()
runCliCommand (UpdateContract uuid endpoint payload) =
    Core.updateContract uuid endpoint payload
runCliCommand (ReportContractHistory uuid) = do
    logInfoN "Contract History"
    itraverse_
        (\index contract ->
             logInfoN $ render (parens (int index) <+> pretty contract)) =<<
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
        do runApp config $ do
               logInfoN $ "Running: " <> Text.pack (show cmd)
               runCliCommand cmd
    case result of
        Left err -> do
            runStdoutLoggingT $ logErrorS err
            exitWith (ExitFailure 1)
        Right _ -> exitWith ExitSuccess
