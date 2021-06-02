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

import           Options.Applicative                     (CommandFields, Mod, Parser, argument, auto, command,
                                                          customExecParser, disambiguate, flag, fullDesc, help, helper,
                                                          idm, info, long, metavar, option, prefs, progDesc, short,
                                                          showHelpOnEmpty, showHelpOnError, str, strOption, subparser,
                                                          value)
import           Plutus.PAB.App                          (EventfulBackend (..))
import           Plutus.PAB.Effects.Contract.ContractExe (ContractExe (..))
import           Wallet.Types                            (ContractInstanceId (..))

data AppOpts = AppOpts { minLogLevel     :: Maybe Severity
                       , logConfigPath   :: Maybe FilePath
                       , configPath      :: Maybe FilePath
                       , runEkgServer    :: Bool
                       , eventfulBackend :: EventfulBackend
                       , cmd             :: Command
                       }

parseOptions :: IO AppOpts
parseOptions = customExecParser
            (prefs $ disambiguate <> showHelpOnEmpty <> showHelpOnError)
            (info (helper <*> commandLineParser) idm)

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

inMemoryFlag :: Parser EventfulBackend
inMemoryFlag =
    flag
        SqliteBackend
        InMemoryBackend
        (short 'm' <> long "memory" <> help "Use the memory-backed eventful backend. If false, the sqlite backend is used.")

commandLineParser :: Parser AppOpts
commandLineParser =
        AppOpts <$> logLevelFlag
               <*> logConfigFileParser
               <*> configFileParser
               <*> ekgFlag
               <*> inMemoryFlag
               <*> commandParser

configFileParser :: Parser (Maybe FilePath)
configFileParser =
    option
        (Just <$> str)
        (long "config" <>
         metavar "CONFIG_FILE" <>
         help "Config file location." <> value Nothing)

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
        outputFile <-
            argument
                str
                (metavar "OUTPUT_FILE" <>
                 help "Output file to write logging config YAML to.")
        pure $ WithoutConfig WriteDefaultConfig {outputFile}

psGeneratorCommandParser :: Mod CommandFields Command
psGeneratorCommandParser =
    command "psgenerator" $
    flip info (fullDesc <> progDesc "Generate the frontend's PureScript files.") $ do
        outputDir <-
            argument
                str
                (metavar "OUTPUT_DIR" <>
                 help "Output directory to write PureScript files to.")
        pure $ WithoutConfig PSGenerator {outputDir}

migrationParser :: Mod CommandFields Command
migrationParser =
    command "migrate" $
    flip info (fullDesc <> progDesc "Update the database with the latest schema.") $ do
        dbPath <-
            argument
                str
                (metavar "DATABASE" <>
                 help "The sqlite database file.")
        pure $ WithoutConfig $ Migrate{dbPath}

mockNodeParser :: Mod CommandFields Command
mockNodeParser =
    command "node-server" $
    info
        (pure $ WithConfig MockNode)
        (fullDesc <> progDesc "Run a mock version of the Cardano node API server.")

mockWalletParser :: Mod CommandFields Command
mockWalletParser =
    command "wallet-server" $
    info
        (pure $ WithConfig MockWallet)
        (fullDesc <>
         progDesc "Run a mock version of the Cardano wallet API server.")

chainIndexParser :: Mod CommandFields Command
chainIndexParser =
    command "chain-index" $
    info (pure $ WithConfig ChainIndex) (fullDesc <> progDesc "Run the chain index.")

metadataParser :: Mod CommandFields Command
metadataParser =
    command "metadata-server" $
    info (pure $ WithConfig Metadata) (fullDesc <> progDesc "Run the Cardano metadata API server.")

allServersParser :: Mod CommandFields Command
allServersParser =
    command "all-servers" $
    info
        (pure $ (WithConfig $ ForkCommands
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
        (pure (WithConfig $ ForkCommands
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
        (WithConfig . InstallContract . ContractExe <$>
         strOption
             (short 'p' <>
              long "path" <> help "Path to the executable contract."))
        (fullDesc <> progDesc "Install a new smart contract.")

contractStateParser :: Mod CommandFields Command
contractStateParser =
    command "state" $
    info
        (WithConfig . ContractState <$> contractIdParser)
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
        (pure $ WithConfig ReportInstalledContracts)
        (fullDesc <> progDesc "Show all installed contracts.")

reportActiveContractsParser :: Mod CommandFields Command
reportActiveContractsParser =
    command "active" $
    info
        (pure $ WithConfig ReportActiveContracts)
        (fullDesc <> progDesc "Show all active contracts.")

pabWebserverParser :: Mod CommandFields Command
pabWebserverParser =
    command "webserver" $
    info
        (pure $ WithConfig PABWebserver)
        (fullDesc <> progDesc "Start the PAB backend webserver.")

reportContractHistoryParser :: Mod CommandFields Command
reportContractHistoryParser =
    command "history" $
    info
        (WithConfig . ReportContractHistory <$> contractIdParser)
        (fullDesc <> progDesc "Show the state history of a smart contract.")
