{-# LANGUAGE ApplicativeDo       #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE RecordWildCards     #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Main
    ( main
    ) where

import           Control.Monad.IO.Class (MonadIO, liftIO)
import           Control.Monad.Logger   (logInfoN, runStderrLoggingT)
import qualified Data.Text              as Text
import           Git                    (gitRev)
import           Options.Applicative    (CommandFields, Mod, Parser, argument, auto, command, customExecParser,
                                         disambiguate, fullDesc, help, helper, idm, info, infoOption, long, metavar,
                                         option, optional, prefs, progDesc, short, showDefault, showHelpOnEmpty,
                                         showHelpOnError, str, subparser, value)
import qualified PSGenerator
import qualified Webserver

data Command
    = Webserver { _port      :: !Int }
    | PSGenerator { _outputDir :: !FilePath }
    deriving (Show, Eq)

versionOption :: Parser (a -> a)
versionOption =
    infoOption
        (Text.unpack gitRev)
        (short 'v' <> long "version" <> help "Show the version")

commandLineParser :: Parser (Maybe FilePath, Command)
commandLineParser = (,) <$> configFileParser <*> commandParser

configFileParser :: Parser (Maybe FilePath)
configFileParser = optional $
    option
        str
        (long "config" <> metavar "CONFIG_FILE" <> help "Config file location.")

commandParser :: Parser Command
commandParser = subparser $ webserverCommandParser <> psGeneratorCommandParser

psGeneratorCommandParser :: Mod CommandFields Command
psGeneratorCommandParser =
    command "psgenerator" $
    flip info (fullDesc <> progDesc "Generate the frontend's PureScript files.") $ do
        _outputDir <-
            argument
                str
                (metavar "OUTPUT_DIR" <>
                 help "Output directory to write PureScript files to.")
        pure PSGenerator {..}

webserverCommandParser :: Mod CommandFields Command
webserverCommandParser =
    command "webserver" $
    flip info fullDesc $ do
        _port <-
            option
                auto
                (short 'p' <> long "port" <> help "Webserver port number" <>
                 showDefault <>
                 value 8080)
        pure Webserver {..}

runCommand :: MonadIO m => Maybe FilePath -> Command -> m ()
runCommand secrets Webserver {..} = liftIO $ Webserver.run _port secrets
runCommand _ PSGenerator {..}     = liftIO $ PSGenerator.generate _outputDir

main :: IO ()
main = do
    options <-
        customExecParser
            (prefs $ disambiguate <> showHelpOnEmpty <> showHelpOnError)
            (info (helper <*> versionOption <*> commandLineParser) idm)
    runStderrLoggingT $ do
        logInfoN $ "Running: " <> Text.pack (show options)
        uncurry runCommand options
