{-# LANGUAGE ApplicativeDo       #-}
{-# LANGUAGE DeriveAnyClass      #-}
{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE DerivingStrategies  #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}

module Main where

import           Control.Monad.IO.Class         (liftIO)
import           Data.Foldable                  (for_)
import           Data.Yaml                      (decodeFileThrow)
import           Options.Applicative            (execParser)

import qualified Cardano.BM.Configuration.Model as CM

import           CommandLine                    (AppConfig (..), cmdWithHelpParser)
import           Config                         (ChainIndexConfig)
import           Logging                        (defaultConfig, loadConfig)

main :: IO ()
main = do
  -- Parse comand line arguments.
  cmdConfig <- execParser cmdWithHelpParser

  -- Initialise logging
  logConfig <- maybe defaultConfig loadConfig (acLogConfigPath cmdConfig)
  for_ (acMinLogLevel cmdConfig) $ \ll -> CM.setMinSeverity logConfig ll

  -- Reading configuration file
  config <- case acConfigPath cmdConfig of
              Nothing -> pure Nothing
              Just p  ->
                Just <$> (liftIO $ decodeFileThrow @_ @ChainIndexConfig p)

  putStrLn "Command line config:"
  print cmdConfig

  putStrLn "Configuration file:"
  print config
