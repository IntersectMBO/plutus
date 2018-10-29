{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE TemplateHaskell #-}

module Main
  ( main
  ) where

import Control.Monad.IO.Class (MonadIO, liftIO)
import Control.Monad.Logger (MonadLogger, logInfoN, runStderrLoggingT)
import Data.Function ((&))
import Data.Monoid ((<>))
import qualified Data.Text as Text
import Development.GitRev (gitHash)
import Network (HostName)
import Network.Wai.Handler.Warp
  ( HostPreference
  , defaultSettings
  , setHost
  , setPort
  )
import Options.Applicative
  ( Parser
  , argument
  , auto
  , customExecParser
  , disambiguate
  , help
  , helper
  , idm
  , info
  , infoOption
  , long
  , metavar
  , option
  , prefs
  , short
  , showDefault
  , str
  , strOption
  , value
  )
import qualified Webserver

data Command = Run
  { _host :: HostPreference
  , _port :: Int
  , _staticDir :: FilePath
  } deriving (Show, Eq)

versionOption :: Parser (a -> a)
versionOption =
  infoOption $(gitHash) (short 'v' <> long "version" <> help "Show the version")

commandParser :: Parser Command
commandParser = do
  _host <-
    strOption
      (short 'b' <> long "bind" <> help "Webserver bind address" <> showDefault <>
       value "127.0.0.1")
  _port <-
    option
      auto
      (short 'p' <> long "port" <> help "Webserver port number" <> showDefault <>
       value 8080)
  _staticDir <-
    argument str (metavar "STATIC_DIR" <> help "Static directory to serve up")
  pure Run {..}

runCommand :: (MonadIO m, MonadLogger m) => Command -> m ()
runCommand Run {..} = do
  logInfoN . Text.pack $ "Running on " <> show _host <> ":" <> show _port
  Webserver.run settings _staticDir
  where
    settings = setHost _host . setPort _port $ defaultSettings

main :: IO ()
main = do
  command <-
    customExecParser
      (prefs disambiguate)
      (info (helper <*> versionOption <*> commandParser) idm)
  runStderrLoggingT $ do
    logInfoN $ "Running: " <> Text.pack (show command)
    runCommand command
