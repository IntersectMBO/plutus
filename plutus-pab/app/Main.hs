{-# LANGUAGE ApplicativeDo         #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DerivingVia           #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns        #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE ScopedTypeVariables   #-}

module Main
    ( main
    ) where

import           Cli
import           Command                                 (Command (..))
import           CommandParser

import qualified Cardano.BM.Backend.EKGView              as EKGView
import qualified Cardano.BM.Configuration.Model          as CM
import           Cardano.BM.Data.Trace                   (Trace)
import           Cardano.BM.Plugin                       (loadPlugin)
import           Cardano.BM.Setup                        (setupTrace_)
import           Control.Concurrent.Availability         (newToken)
import           Control.Monad                           (when)
import           Control.Monad.IO.Class                  (liftIO)
import           Control.Monad.Logger                    (logErrorN, runStdoutLoggingT)
import           Data.Foldable                           (for_)
import           Data.Text.Extras                        (tshow)
import           Data.Yaml                               (decodeFileThrow)
import           Plutus.PAB.Effects.Contract.ContractExe (ContractExe)
import           Plutus.PAB.Monitoring.Config            (defaultConfig, loadConfig)
import           Plutus.PAB.Monitoring.PABLogMsg         (AppMsg (..))
import           Plutus.PAB.Monitoring.Util              (PrettyObject (..), convertLog)
import           Plutus.PAB.Types                        (PABError (MissingConfigFileOption))
import           System.Exit                             (ExitCode (ExitFailure), exitSuccess, exitWith)

main :: IO ()
main = do
    AppOpts { minLogLevel, logConfigPath, runEkgServer, cmd, configPath, eventfulBackend } <- parseOptions

    -- Parse config files and initialize logging
    logConfig <- maybe defaultConfig loadConfig logConfigPath
    for_ minLogLevel $ \ll -> CM.setMinSeverity logConfig ll
    (trace :: Trace IO (PrettyObject (AppMsg ContractExe)), switchboard) <- setupTrace_ logConfig "pab"

    -- enable EKG backend
    when runEkgServer $ EKGView.plugin logConfig trace switchboard >>= loadPlugin switchboard

    -- obtain token for signaling service readiness
    serviceAvailability <- newToken

    -- execute parsed pab command and handle errors on faliure
    result <- case cmd of
                WithConfig command -> do
                    case configPath of
                        Nothing -> pure $ Left MissingConfigFileOption
                        Just p -> do
                            config <- liftIO $ decodeFileThrow p
                            Right <$> runConfigCommand (convertLog PrettyObject trace) logConfig config serviceAvailability eventfulBackend command
                WithoutConfig command -> Right <$> runNoConfigCommand (convertLog PrettyObject trace) command
    either handleError (const exitSuccess) result

        where

            handleError (err :: PABError) = do
                runStdoutLoggingT $ (logErrorN . tshow) err
                exitWith (ExitFailure 1)
