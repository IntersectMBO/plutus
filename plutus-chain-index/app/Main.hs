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
import           Control.Exception                   (throwIO)
import           Control.Lens                        (unto)
import           Control.Monad.Freer                 (Eff, interpret, reinterpret, run, send)
import           Control.Monad.Freer.Error           (Error, runError)
import           Control.Monad.Freer.Extras          (LogMsg (..))
import           Control.Monad.Freer.Extras.Log      (LogLevel (..), LogMessage (..), handleLogWriter)
import           Control.Monad.Freer.State           (State, runState)
import           Control.Monad.Freer.Writer          (runWriter)
import           Control.Monad.IO.Class              (liftIO)
import qualified Data.Aeson                          as A
import           Data.Foldable                       (for_, traverse_)
import           Data.Function                       ((&))
import           Data.Functor                        (void)
import           Data.Sequence                       (Seq, (<|))
import           Data.Text.Prettyprint.Doc           (Pretty (..))
import qualified Data.Yaml                           as Y
import           Options.Applicative                 (execParser)
import qualified Plutus.ChainIndex.Server            as Server

import qualified Cardano.BM.Configuration.Model      as CM
import           Cardano.BM.Setup                    (setupTrace_)
import           Cardano.BM.Trace                    (Trace, logError)

import           Cardano.Protocol.Socket.Client      (ChainSyncEvent (..), runChainSync)
import           CommandLine                         (AppConfig (..), Command (..), applyOverrides, cmdWithHelpParser)
import qualified Config
import           Ledger                              (Slot (..))
import qualified Logging
import           Plutus.ChainIndex.ChainIndexError   (ChainIndexError (..))
import           Plutus.ChainIndex.ChainIndexLog     (ChainIndexLog (..))
import           Plutus.ChainIndex.Compatibility     (fromCardanoBlock, fromCardanoPoint, tipFromCardanoBlock)
import           Plutus.ChainIndex.Effects           (ChainIndexControlEffect (..), ChainIndexQueryEffect (..),
                                                      appendBlock, rollback)
import           Plutus.ChainIndex.Emulator.Handlers (ChainIndexEmulatorState (..), handleControl, handleQuery)
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
          = effect
          & interpret handleControl
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
  (RollForward block _) _ = do
    let ciBlock = fromCardanoBlock block
    case ciBlock of
      Left err    ->
        logError trace (ConversionFailed err)
      Right txs ->
        runChainIndex trace mState $ appendBlock (tipFromCardanoBlock block) txs
chainSyncHandler trace mState
  (RollBackward point _) _ = do
    -- Do we really want to pass the tip of the new blockchain to the
    -- rollback function (rather than the point where the chains diverge)?
    runChainIndex trace mState $ rollback (fromCardanoPoint point)
-- On resume we do nothing, for now.
chainSyncHandler _ _ (Resume _) _ = do
  pure ()

main :: IO ()
main = do
  -- Parse comand line arguments.
  cmdConfig@AppConfig{acLogConfigPath, acConfigPath, acMinLogLevel, acCommand, acCLIConfigOverrides} <- execParser cmdWithHelpParser

  case acCommand of
    DumpDefaultConfig path ->
      A.encodeFile path Config.defaultConfig

    DumpDefaultLoggingConfig path ->
      Logging.defaultConfig >>= CM.toRepresentation >>= Y.encodeFile path

    StartChainIndex{} -> do
      -- Initialise logging
      logConfig <- maybe Logging.defaultConfig Logging.loadConfig acLogConfigPath
      for_ acMinLogLevel $ \ll -> CM.setMinSeverity logConfig ll
      (trace :: Trace IO ChainIndexLog, _) <- setupTrace_ logConfig "chain-index"

      -- Reading configuration file
      config <- applyOverrides acCLIConfigOverrides <$> case acConfigPath of
        Nothing -> pure Config.defaultConfig
        Just p  -> A.eitherDecodeFileStrict p >>=
          either (throwIO . Config.DecodeConfigException) pure

      putStrLn "\nCommand line config:"
      print cmdConfig

      putStrLn "\nLogging config:"
      CM.toRepresentation logConfig >>= print

      putStrLn "\nChain Index config:"
      print (pretty config)

      appState <- STM.newTVarIO mempty

      putStrLn $ "Connecting to the node using socket: " <> Config.cicSocketPath config
      void $ runChainSync (Config.cicSocketPath config)
                          (Config.cicSlotConfig config)
                          (Config.cicNetworkId  config)
                          []
                          (chainSyncHandler trace appState)

      putStrLn $ "Starting webserver on port " <> show (Config.cicPort config)
      Server.serveChainIndexQueryServer (Config.cicPort config) appState
