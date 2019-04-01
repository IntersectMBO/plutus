{-# LANGUAGE ApplicativeDo       #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE RecordWildCards     #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}

module Main
    ( main
    ) where

import           Control.Monad.IO.Class   (MonadIO, liftIO)
import           Control.Monad.Logger     (MonadLogger, logInfoN, runStderrLoggingT)
import           Data.Monoid              ((<>))
import qualified Data.Text                as Text
import           Data.Yaml                (decodeFileThrow)
import           Development.GitRev       (gitHash)
import           Network.Wai.Handler.Warp (HostPreference, defaultSettings, setHost, setPort)
import           Options.Applicative      (CommandFields, Mod, Parser, argument, auto, command, customExecParser,
                                           disambiguate, fullDesc, help, helper, idm, info, infoOption, long, metavar,
                                           option, prefs, short, showDefault, showHelpOnEmpty, str, strOption,
                                           subparser, value)
import qualified PSGenerator
import qualified Webserver

-- | You might wonder why we don't stick everything in `Config`. The
-- answer is that pushing certain flags to the command line makes
-- automated deployment easier.
--
-- You might also wonder why we don't stick everything on the command
-- line. The answer is for flags that rarely change, putting them in a
-- config file makes development easier.
data Command
    = Webserver { _host      :: !HostPreference
                , _port      :: !Int
                , _staticDir :: !FilePath }
    | PSGenerator { _outputDir :: !FilePath }
    deriving (Show, Eq)

versionOption :: Parser (a -> a)
versionOption =
    infoOption
        $(gitHash)
        (short 'v' <> long "version" <> help "Show the version")

commandLineParser :: Parser (FilePath, Command)
commandLineParser = (,) <$> configFileParser <*> commandParser

configFileParser :: Parser FilePath
configFileParser =
    option
        str
        (long "config" <> metavar "CONFIG_FILE" <> help "Config file location." <>
         value "playground.yaml")

commandParser :: Parser Command
commandParser = subparser $ webserverCommandParser <> psGeneratorCommandParser

psGeneratorCommandParser :: Mod CommandFields Command
psGeneratorCommandParser =
    command "psgenerator" $
    flip info fullDesc $ do
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
        _host <-
            strOption
                (short 'b' <> long "bind" <> help "Webserver bind address" <>
                 showDefault <>
                 value "127.0.0.1")
        _port <-
            option
                auto
                (short 'p' <> long "port" <> help "Webserver port number" <>
                 showDefault <>
                 value 8080)
        _staticDir <-
            argument
                str
                (metavar "STATIC_DIR" <> help "Static directory to serve up")
        pure Webserver {..}

runCommand :: (MonadIO m, MonadLogger m) => FilePath -> Command -> m ()
runCommand configPath Webserver {..} = do
    config <- liftIO $ decodeFileThrow configPath
    Webserver.run settings _staticDir config
  where
    settings = setHost _host . setPort _port $ defaultSettings
runCommand _ PSGenerator {..} = liftIO $ PSGenerator.generate _outputDir

main :: IO ()
main = do
    options <-
        customExecParser
            (prefs $ disambiguate <> showHelpOnEmpty)
            (info (helper <*> versionOption <*> commandLineParser) idm)
    runStderrLoggingT $ do
        logInfoN $ "Running: " <> Text.pack (show options)
        uncurry runCommand options
