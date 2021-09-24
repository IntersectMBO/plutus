{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE DeriveAnyClass      #-}
{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE DerivingStrategies  #-}
{-# LANGUAGE NamedFieldPuns      #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}

module Main where

import qualified Control.Concurrent.STM            as STM
import           Control.Exception                 (throwIO)
import           Control.Lens                      (unto)
import           Control.Monad.Freer               (Eff, interpret, reinterpret, runM, send)
import           Control.Monad.Freer.Error         (Error, runError)
import           Control.Monad.Freer.Extras        (LogMsg (..))
import           Control.Monad.Freer.Extras.Log    (LogLevel (..), LogMessage (..), handleLogWriter)
import           Control.Monad.Freer.State         (State, runState)
import           Control.Monad.Freer.Writer        (runWriter)
import           Control.Tracer                    (nullTracer)
import qualified Data.Aeson                        as A
import           Data.Foldable                     (for_, traverse_)
import           Data.Function                     ((&))
import           Data.Functor                      (void)
import           Data.Sequence                     (Seq, (<|))
import           Data.Text.Prettyprint.Doc         (Pretty (..))
import qualified Data.Yaml                         as Y
import           Database.Beam.Migrate.Simple      (autoMigrate)
import qualified Database.Beam.Sqlite              as Sqlite
import qualified Database.Beam.Sqlite.Migrate      as Sqlite
import qualified Database.SQLite.Simple            as Sqlite
import           Options.Applicative               (execParser)
import qualified Plutus.ChainIndex.Server          as Server

import qualified Cardano.BM.Configuration.Model    as CM
import           Cardano.BM.Setup                  (setupTrace_)
import           Cardano.BM.Trace                  (Trace, logDebug, logError)

import           Cardano.Protocol.Socket.Client    (ChainSyncEvent (..), runChainSync)
import           CommandLine                       (AppConfig (..), Command (..), applyOverrides, cmdWithHelpParser)
import qualified Config
import           Ledger                            (Slot (..))
import qualified Logging
import           Plutus.ChainIndex.ChainIndexError (ChainIndexError (..))
import           Plutus.ChainIndex.ChainIndexLog   (ChainIndexLog (..))
import           Plutus.ChainIndex.Compatibility   (fromCardanoBlock, fromCardanoPoint, tipFromCardanoBlock)
import           Plutus.ChainIndex.DbStore         (DbStoreEffect, checkedSqliteDb, handleDbStore)
import           Plutus.ChainIndex.Effects         (ChainIndexControlEffect (..), ChainIndexQueryEffect (..),
                                                    appendBlock, rollback)
import           Plutus.ChainIndex.Handlers        (ChainIndexState, getResumePoints, handleControl, handleQuery,
                                                    restoreStateFromDb)
import           Plutus.Monitoring.Util            (runLogEffects)

type ChainIndexEffects
  = '[ ChainIndexControlEffect
     , ChainIndexQueryEffect
     , DbStoreEffect
     , State ChainIndexState
     , Error ChainIndexError
     , LogMsg ChainIndexLog
     , IO
     ]

runChainIndex
  :: Trace IO ChainIndexLog
  -> STM.TVar ChainIndexState
  -> Sqlite.Connection
  -> Eff ChainIndexEffects a
  -> IO a
runChainIndex trace mState conn effect = do
  -- First run the STM block capturing all log messages emited on a
  -- successful STM transaction.
  oldEmulatorState <- STM.atomically $ STM.readTVar mState
  (errOrResult, logMessages') <-
    effect
    & interpret handleControl
    & interpret handleQuery
    & interpret (handleDbStore trace conn)
    & runState oldEmulatorState
    & runError
    & reinterpret
        (handleLogWriter @ChainIndexLog
                          @(Seq (LogMessage ChainIndexLog)) $ unto pure)
    & runWriter @(Seq (LogMessage ChainIndexLog))
    & runM
  (result, logMessages) <- case errOrResult of
      Left err ->
        pure (fail $ show err, LogMessage Error (Err err) <| logMessages')
      Right (result, newState) -> do
        STM.atomically $ STM.writeTVar mState newState
        pure (pure result, logMessages')
  -- Log all previously captured messages
  traverse_ (send . LMessage) logMessages
    & runLogEffects trace
  result

chainSyncHandler
  :: Trace IO ChainIndexLog
  -> STM.TVar ChainIndexState
  -> Sqlite.Connection
  -> ChainSyncEvent
  -> Slot
  -> IO ()
chainSyncHandler trace mState conn
  (RollForward block _) _ = do
    let ciBlock = fromCardanoBlock block
    case ciBlock of
      Left err    ->
        logError trace (ConversionFailed err)
      Right txs ->
        void $ runChainIndex trace mState conn $ appendBlock (tipFromCardanoBlock block) txs
chainSyncHandler trace mState conn
  (RollBackward point _) _ = do
    putStr "Rolling back to "
    print point
    -- Do we really want to pass the tip of the new blockchain to the
    -- rollback function (rather than the point where the chains diverge)?
    void $ runChainIndex trace mState conn $ rollback (fromCardanoPoint point)
chainSyncHandler trace mState conn
  (Resume point) _ = do
    putStr "Resuming from "
    print point
    newState <- runChainIndex trace mState conn $ restoreStateFromDb $ fromCardanoPoint point
    putStrLn "New state:"
    print newState
    STM.atomically $ STM.writeTVar mState newState



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

      Sqlite.withConnection (Config.cicDbPath config) $ \conn -> do

        Sqlite.runBeamSqliteDebug (logDebug trace . SqlLog) conn $ do
          autoMigrate Sqlite.migrationBackend checkedSqliteDb

        appState <- STM.newTVarIO mempty
        resumePoints <- runChainIndex trace appState conn getResumePoints

        putStr "\nNumber of possible resume points: "
        print $ length resumePoints

        putStrLn $ "Connecting to the node using socket: " <> Config.cicSocketPath config
        void $ runChainSync (Config.cicSocketPath config)
                            nullTracer
                            (Config.cicSlotConfig config)
                            (Config.cicNetworkId  config)
                            resumePoints
                            (chainSyncHandler trace appState conn)

        putStrLn $ "Starting webserver on port " <> show (Config.cicPort config)
        Server.serveChainIndexQueryServer (Config.cicPort config) trace appState conn
