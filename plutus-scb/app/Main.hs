{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE OverloadedStrings #-}

module Main
    ( main
    ) where

import qualified Cardano.Node.Client       as NodeClient
import qualified Cardano.Node.MockServer   as NodeServer
import qualified Cardano.Wallet.Client     as WalletClient
import qualified Cardano.Wallet.MockServer as WalletServer
import           Control.Monad.IO.Unlift   (MonadUnliftIO, liftIO)
import           Control.Monad.Logger      (LogLevel (LevelDebug), MonadLogger, filterLogger, logDebugN, logInfoN,
                                            runStderrLoggingT)
import           Control.Monad.Reader      (MonadReader, runReaderT)
import           Data.Foldable             (traverse_)
import qualified Data.Text                 as Text
import           Data.Yaml                 (decodeFileThrow)
import           Git                       (gitRev)
import           Options.Applicative       (CommandFields, Mod, Parser, auto, command, customExecParser, disambiguate,
                                            fullDesc, help, helper, idm, info, infoOption, long, metavar, option,
                                            optional, prefs, progDesc, short, showHelpOnEmpty, showHelpOnError, str,
                                            strOption, subparser, value)
import           Plutus.SCB.Core           (SCBError)
import qualified Plutus.SCB.Core           as Core
import           Plutus.SCB.Utils          (logErrorS)
import           System.Exit               (ExitCode (ExitFailure, ExitSuccess), exitWith)
import qualified System.Remote.Monitoring  as EKG

data Command
    = DbStats
    | Simulate
    | Migrate
    | MockNode
    | MockWallet
    | WalletClient
    | NodeClient
    | InstallContract FilePath
    | ListAvailableContracts
    | ListActiveContracts
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
        (long "monitoring-port" <> short 'p' <> metavar "PORT" <>
         help "Open an EKG server on PORT")

configFileParser :: Parser FilePath
configFileParser =
    option
        str
        (long "config" <> metavar "CONFIG_FILE" <> help "Config file location." <>
         value "plutus-scb.yaml")

commandParser :: Parser Command
commandParser =
    subparser $
    mconcat
        [ simulationParser
        , migrationParser
        , dbStatsParser
        , mockWalletParser
        , walletClientParser
        , mockNodeParser
        , nodeClientParser
        , installContractParser
        , listAvailableContractsParser
        , listActiveContractsParser
        ]

dbStatsParser :: Mod CommandFields Command
dbStatsParser =
    command "stats" $
    info
        (pure DbStats)
        (fullDesc <> progDesc "Report some useful database statistics.")

migrationParser :: Mod CommandFields Command
migrationParser =
    command "migrate" $
    info
        (pure Migrate)
        (fullDesc <> progDesc "Update the database with the latest schema.")

simulationParser :: Mod CommandFields Command
simulationParser =
    command "simulate" $
    info
        (pure Simulate)
        (fullDesc <> progDesc "Seed the event stream with simulated events.")

mockNodeParser :: Mod CommandFields Command
mockNodeParser =
    command "mock-node" $
    info
        (pure MockNode)
        (fullDesc <>
         progDesc "Run a mock version of the Cardano node API server.")

mockWalletParser :: Mod CommandFields Command
mockWalletParser =
    command "mock-wallet" $
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

nodeClientParser :: Mod CommandFields Command
nodeClientParser =
    command "node-client" $
    info
        (pure NodeClient)
        (fullDesc <> progDesc "Run a basic query against the Cardano node API.")

installContractParser :: Mod CommandFields Command
installContractParser =
    command "install" $
    flip
        info
        (fullDesc <> progDesc "Install a new smart contract.")
        (InstallContract <$>
         strOption
             (short 'p' <> long "path" <>
              help "Path to contract. Must be an executable."))

listAvailableContractsParser :: Mod CommandFields Command
listAvailableContractsParser =
    command "available-contracts" $
    info
        (pure ListAvailableContracts)
        (fullDesc <> progDesc "Show all installed contracts.")

listActiveContractsParser :: Mod CommandFields Command
listActiveContractsParser =
    command "contracts" $
    info
        (pure ListActiveContracts)
        (fullDesc <> progDesc "Show all active contracts.")

------------------------------------------------------------
runCliCommand ::
       (MonadLogger m, MonadUnliftIO m, MonadReader Core.DbConfig m)
    => Command
    -> m (Either SCBError ())
runCliCommand Simulate               = Right <$> Core.simulate
runCliCommand DbStats                = Right <$> Core.dbStats
runCliCommand Migrate                = Right <$> Core.migrate
runCliCommand MockWallet             = Right <$> WalletServer.main
runCliCommand MockNode               = Right <$> NodeServer.main
runCliCommand WalletClient           = Right <$> liftIO WalletClient.main
runCliCommand NodeClient             = Right <$> liftIO NodeClient.main
runCliCommand (InstallContract path) = Core.installContract path
runCliCommand ListAvailableContracts = Right <$> Core.listAvailableContracts
runCliCommand ListActiveContracts    = Right <$> Core.listActiveContracts

main :: IO ()
main = do
    (ekgPort, configPath, cmd) <-
        customExecParser
            (prefs $ disambiguate <> showHelpOnEmpty <> showHelpOnError)
            (info (helper <*> versionOption <*> commandLineParser) idm)
    config <- liftIO $ decodeFileThrow configPath
    traverse_ (EKG.forkServer "localhost") ekgPort
    returnCode <-
        runStderrLoggingT $
        filterLogger (\_ level -> level > LevelDebug) $ do
            logInfoN $ "Running: " <> Text.pack (show cmd)
            result <- runReaderT (runCliCommand cmd) config
            logDebugN $ "Ran: " <> Text.pack (show result)
            case result of
                Left err -> do
                    logErrorS err
                    pure (ExitFailure 1)
                Right () -> pure ExitSuccess
    exitWith returnCode
