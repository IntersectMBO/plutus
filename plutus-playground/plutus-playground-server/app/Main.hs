{-# LANGUAGE ApplicativeDo     #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards   #-}
{-# LANGUAGE TemplateHaskell   #-}

module Main
  ( main
  ) where

import           Control.Monad.IO.Class   (MonadIO, liftIO)
import           Control.Monad.Logger     (MonadLogger, logInfoN, runStderrLoggingT)
import           Data.Monoid              ((<>))
import qualified Data.Text                as Text
import           Development.GitRev       (gitHash)
import           Network.Wai.Handler.Warp (HostPreference, defaultSettings, setHost, setPort)
import           Options.Applicative      (CommandFields, Mod, Parser, argument, auto, command, customExecParser,
                                           disambiguate, fullDesc, help, helper, idm, info, infoOption, long, metavar,
                                           option, prefs, short, showDefault, str, strOption, subparser, value)
import qualified PSGenerator
import qualified Webserver

data Command
  = Webserver { _host      :: HostPreference
              , _port      :: Int
              , _staticDir :: FilePath }
  | PSGenerator { _outputDir :: FilePath }
  deriving (Show, Eq)

versionOption :: Parser (a -> a)
versionOption =
  infoOption $(gitHash) (short 'v' <> long "version" <> help "Show the version")

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
        (short 'p' <> long "port" <> help "Webserver port number" <> showDefault <>
         value 8080)
    _staticDir <-
      argument str (metavar "STATIC_DIR" <> help "Static directory to serve up")
    pure Webserver {..}

runCommand :: (MonadIO m, MonadLogger m) => Command -> m ()
runCommand Webserver {..} = do
  logInfoN . Text.pack $ "Running on " <> show _host <> ":" <> show _port
  Webserver.run settings _staticDir
  where
    settings = setHost _host . setPort _port $ defaultSettings
runCommand PSGenerator {..} =
  liftIO $ PSGenerator.generate _outputDir

main :: IO ()
main = do
  cmd <-
    customExecParser
      (prefs disambiguate)
      (info (helper <*> versionOption <*> commandParser) idm)
  runStderrLoggingT $ do
    logInfoN $ "Running: " <> Text.pack (show cmd)
    runCommand cmd
