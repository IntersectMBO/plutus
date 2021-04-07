{-# LANGUAGE ApplicativeDo         #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DerivingVia           #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns        #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE ScopedTypeVariables   #-}

module CommandParser (parseOptions, AppOpts(..)) where

import           Command

import           Cardano.BM.Data.Severity                (Severity (..))
import qualified Data.Text                               as Text

import           Git                                     (gitRev)
import           Options.Applicative                     (CommandFields, Mod, Parser, argument, auto, command,
                                                          customExecParser, disambiguate, flag, fullDesc, help, helper,
                                                          idm, info, infoOption, long, metavar, option, prefs, progDesc,
                                                          short, showHelpOnEmpty, showHelpOnError, str, strOption,
                                                          subparser, value)
import           Plutus.PAB.Effects.Contract.ContractExe (ContractExe (..))
import           Wallet.Types                            (ContractInstanceId (..))

data AppOpts = AppOpts { minLogLevel   :: Maybe Severity
                       , configPath    :: FilePath
                       , logConfigPath :: Maybe FilePath
                       , runEkgServer  :: Bool
                       , cmd           :: Command
                       }

parseOptions :: IO AppOpts
parseOptions = customExecParser
            (prefs $ disambiguate <> showHelpOnEmpty <> showHelpOnError)
            (info (helper <*> versionOption <*> commandLineParser) idm)

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

ekgFlag :: Parser Bool
ekgFlag =
    flag
        False
        True
        (short 'e' <> long "ekg" <> help "Enable the EKG server")

commandLineParser :: Parser AppOpts
commandLineParser =
        AppOpts <$> logLevelFlag
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
        , defaultConfigParser
        , simulatorParser
        , command
              "contracts"
              (info
                   (subparser
                        (mconcat
                             [ installContractParser
                             , reportInstalledContractsParser
                             , reportActiveContractsParser
                             , contractStateParser
                             , reportContractHistoryParser
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

simulatorParser :: Mod CommandFields Command
simulatorParser =
    command "simulator" $
    info
        (pure StartSimulatorWebServer)
        (fullDesc <> progDesc "Start a simulator with some pre-installed contracts. No external services required.")

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
                  ]))
        (fullDesc <> progDesc "Run the client services (all services except the mock node).")

installContractParser :: Mod CommandFields Command
installContractParser =
    command "install" $
    info
        (InstallContract . ContractExe <$>
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

contractIdParser :: Parser ContractInstanceId
contractIdParser = fmap ContractInstanceId $
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

pabWebserverParser :: Mod CommandFields Command
pabWebserverParser =
    command "webserver" $
    info
        (pure PABWebserver)
        (fullDesc <> progDesc "Start the PAB backend webserver.")

reportContractHistoryParser :: Mod CommandFields Command
reportContractHistoryParser =
    command "history" $
    info
        (ReportContractHistory <$> contractIdParser)
        (fullDesc <> progDesc "Show the state history of a smart contract.")
