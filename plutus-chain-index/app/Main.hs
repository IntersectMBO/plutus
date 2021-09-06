{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE DeriveAnyClass      #-}
{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE DerivingStrategies  #-}
{-# LANGUAGE NamedFieldPuns      #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}

module Main where

import qualified Control.Concurrent.STM              as STM
import           Control.Lens                        (unto)
import           Control.Monad.Freer                 (Eff, interpret, reinterpret, run, send)
import           Control.Monad.Freer.Error           (Error, runError)
import           Control.Monad.Freer.Extras          (LogMsg (..))
import           Control.Monad.Freer.Extras.Log      (LogLevel (..), LogMessage (..), handleLogWriter)
import           Control.Monad.Freer.State           (State, runState)
import           Control.Monad.Freer.Writer          (runWriter)
import           Control.Monad.IO.Class              (liftIO)
import           Data.Foldable                       (for_, traverse_)
import           Data.Function                       ((&))
import           Data.Functor                        (void)
import           Data.Sequence                       (Seq, (<|))
import           Data.Text.Prettyprint.Doc           (Pretty (..))
import           Data.Yaml                           (decodeFileThrow)
import           Options.Applicative                 (execParser)
import qualified Plutus.ChainIndex.Server            as Server

import qualified Cardano.BM.Configuration.Model      as CM
import           Cardano.BM.Setup                    (setupTrace_)
import           Cardano.BM.Trace                    (Trace, logError)

import           Cardano.Protocol.Socket.Client      (ChainSyncEvent (..), runChainSync)
import           CommandLine                         (AppConfig (..), Command (..), cmdWithHelpParser)
import           Config                              (ChainIndexConfig)
import qualified Config                              as Config
import           Ledger                              (Slot (..))
import           Logging                             (defaultConfig, loadConfig)
import           Plutus.ChainIndex.Compatibility     (fromCardanoBlock, fromCardanoTip)
import           Plutus.ChainIndex.Effects           (ChainIndexControlEffect (..), ChainIndexQueryEffect (..),
                                                      appendBlock, rollback)
import           Plutus.ChainIndex.Emulator.Handlers (ChainIndexEmulatorState (..), ChainIndexError (..),
                                                      ChainIndexLog (..), handleControl, handleQuery)
import           Plutus.Monitoring.Util              (runLogEffects)

type ChainIndexEffects
  = '[ ChainIndexControlEffect
     , ChainIndexQueryEffect
     , State ChainIndexEmulatorState
     , Error ChainIndexError
     , LogMsg ChainIndexLog
     ]

runChainIndex
  :: Trace IO ChainIndexLog
  -> STM.TVar ChainIndexEmulatorState
  -> Eff ChainIndexEffects a
  -> IO ()
runChainIndex trace emulatorState effect = do
  -- First run the STM block capturing all log messages emited on a
  -- successful STM transaction.
  logMessages <- liftIO $ STM.atomically $ do
    oldEmulatorState <- STM.readTVar emulatorState
    let (result, logMessages')
          = interpret handleControl effect
          & interpret handleQuery
          & runState oldEmulatorState
          & runError
          & reinterpret
              (handleLogWriter @ChainIndexLog
                               @(Seq (LogMessage ChainIndexLog)) $ unto pure)
          & runWriter @(Seq (LogMessage ChainIndexLog))
          & run
    case result of
      Left err ->
        -- TODO: log the error
        pure $ LogMessage Error (Err err) <| logMessages'
      Right (_, newState) -> do
        STM.writeTVar emulatorState newState
        pure logMessages'
  -- Log all previously captured messages
  traverse_ (send . LMessage) logMessages
    & runLogEffects trace

chainSyncHandler
  :: Trace IO ChainIndexLog
  -> STM.TVar ChainIndexEmulatorState
  -> ChainSyncEvent
  -> Slot
  -> IO ()
chainSyncHandler trace mState
  (RollForward block tip) _ = do
    let ciBlock = fromCardanoBlock block
    case ciBlock of
      Left err    ->
        logError trace (ConversionFailed err)
      Right block' ->
        runChainIndex trace mState $ appendBlock (fromCardanoTip tip) block'
chainSyncHandler trace mState
  (RollBackward _ tip) _ =
    -- Do we really want to pass the tip of the new blockchain to the
    -- rollback function (rather than the point where the chains diverge)?
    runChainIndex trace mState $ rollback (fromCardanoTip tip)
-- On resume we do nothing, for now.
chainSyncHandler _ _ (Resume _) _ = pure ()

main :: IO ()
main = do
  -- Parse comand line arguments.
  cmdConfig@AppConfig{acLogConfigPath, acConfigPath, acMinLogLevel, acCommand} <- execParser cmdWithHelpParser

  -- Initialise logging
  logConfig <- maybe defaultConfig loadConfig acLogConfigPath
  for_ acMinLogLevel $ \ll -> CM.setMinSeverity logConfig ll
  (trace :: Trace IO ChainIndexLog, _) <- setupTrace_ logConfig "chain-index"

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
      putStrLn $ "Connecting to the node using socket: " <> Config.cicSocketPath config
      void $ runChainSync (Config.cicSocketPath config)
                          (Config.cicSlotConfig config)
                          (Config.cicNetworkId config)
                          []
                          (chainSyncHandler trace appState)
      putStrLn $ "Starting webserver on port " <> show (Config.cicPort config)
      Server.serveChainIndexQueryServer (Config.cicPort config) appState
    _ -> pure ()
