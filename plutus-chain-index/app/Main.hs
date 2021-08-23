{-# LANGUAGE ApplicativeDo       #-}
{-# LANGUAGE DeriveAnyClass      #-}
{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE DerivingStrategies  #-}
{-# LANGUAGE NamedFieldPuns      #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}

module Main where

import qualified Control.Concurrent.STM         as STM
import           Data.Foldable                  (for_)
import           Data.Text.Prettyprint.Doc      (Pretty (..))
import           Data.Yaml                      (decodeFileThrow)
import           Options.Applicative            (execParser)
import qualified Plutus.ChainIndex.Server       as Server

import qualified Cardano.BM.Configuration.Model as CM

import           CommandLine                    (AppConfig (..), Command (..), cmdWithHelpParser)
import           Config                         (ChainIndexConfig)
import qualified Config                         as Config
import           Logging                        (defaultConfig, loadConfig)

main :: IO ()
main = do
  -- Parse comand line arguments.
  cmdConfig@AppConfig{acLogConfigPath, acConfigPath, acMinLogLevel, acCommand} <- execParser cmdWithHelpParser

  -- Initialise logging
  logConfig <- maybe defaultConfig loadConfig acLogConfigPath
  for_ acMinLogLevel $ \ll -> CM.setMinSeverity logConfig ll

  -- Reading configuration file
  config <- case acConfigPath of
              Nothing -> pure Config.defaultConfig
              Just p  -> decodeFileThrow @IO @ChainIndexConfig p

  putStrLn "Command line config:"
  print cmdConfig

  putStrLn "Configuration file:"
  print (pretty config)

  appState <- STM.newTVarIO mempty

  case acCommand of
    StartChainIndex{} -> do
      putStrLn $ "Starting webserver on port " <> show (Config.cicPort config)
      Server.serveChainIndexQueryServer (Config.cicPort config) appState
    _ -> pure ()
