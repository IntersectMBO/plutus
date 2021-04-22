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
import           Plutus.PAB.Types                        (PABError)
import           System.Exit                             (ExitCode (ExitFailure), exitSuccess, exitWith)

main :: IO ()
main = do
    AppOpts { minLogLevel, configPath, logConfigPath, runEkgServer, cmd } <- parseOptions

    -- Parse config files and initialize logging
    config <- liftIO $ decodeFileThrow configPath
    logConfig <- maybe defaultConfig loadConfig logConfigPath
    for_ minLogLevel $ \ll -> CM.setMinSeverity logConfig ll
    (trace :: Trace IO (AppMsg ContractExe), switchboard) <- setupTrace_ logConfig "pab"

    -- enable EKG backend
    when runEkgServer $ EKGView.plugin logConfig trace switchboard >>= loadPlugin switchboard

    -- obtain token for signaling service readiness
    serviceAvailability <- newToken

    -- execute parsed pab command and handle errors on faliure
    result <- executePABCommand trace logConfig config serviceAvailability cmd
    either handleError (const exitSuccess) result

        where

            handleError (err :: PABError) = do
                runStdoutLoggingT $ (logErrorN . tshow) err
                exitWith (ExitFailure 1)

            executePABCommand t logConfig config availability cmd =
                fmap Right
                $ runCliCommand t logConfig config availability cmd
                -- runApp (convertLog PABMsg t) logConfig config
                -- $ handleLogMsgTrace (monadLoggerTracer t)
                -- $ runCliCommand t logConfig config availability cmd
