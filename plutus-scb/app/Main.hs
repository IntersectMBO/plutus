{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE OverloadedStrings #-}

module Main
    ( main
    ) where

import           Control.Monad.IO.Unlift  (MonadUnliftIO, liftIO)
import           Control.Monad.Logger     (LogLevel (LevelDebug), MonadLogger, filterLogger, logInfoN,
                                           runStderrLoggingT)
import           Control.Monad.Reader     (MonadReader, runReaderT)
import           Data.Foldable            (traverse_)
import qualified Data.Text                as Text
import           Data.Yaml                (decodeFileThrow)
import           Git                      (gitRev)
import           Options.Applicative      (CommandFields, Mod, Parser, auto, command, customExecParser, disambiguate,
                                           fullDesc, help, helper, idm, info, infoOption, long, metavar, option,
                                           optional, prefs, short, showHelpOnEmpty, str, subparser, value)
import qualified Plutus.SCB.Core          as Core
import qualified System.Remote.Monitoring as EKG

data Command
    = DbStats
    | Simulate
    | Migrate
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
    simulationCommandParser <> migrationCommandParser <> dbStatsCommandParser

dbStatsCommandParser :: Mod CommandFields Command
dbStatsCommandParser = command "stats" $ flip info fullDesc $ pure DbStats

migrationCommandParser :: Mod CommandFields Command
migrationCommandParser = command "migrate" $ flip info fullDesc $ pure Migrate

simulationCommandParser :: Mod CommandFields Command
simulationCommandParser =
    command "simulate" $ flip info fullDesc $ pure Simulate

------------------------------------------------------------
runCliCommand ::
       (MonadLogger m, MonadUnliftIO m, MonadReader Core.DbConfig m)
    => Command
    -> m ()
runCliCommand Simulate = Core.simulate
runCliCommand DbStats  = Core.dbStats
runCliCommand Migrate  = Core.migrate

main :: IO ()
main = do
    (ekgPort, configPath, cmd) <-
        customExecParser
            (prefs $ disambiguate <> showHelpOnEmpty)
            (info (helper <*> versionOption <*> commandLineParser) idm)
    config <- liftIO $ decodeFileThrow configPath
    traverse_ (EKG.forkServer "localhost") ekgPort
    runStderrLoggingT $
        filterLogger (\_ level -> level > LevelDebug) $ do
            logInfoN $ "Running: " <> Text.pack (show cmd)
            runReaderT (runCliCommand cmd) config
