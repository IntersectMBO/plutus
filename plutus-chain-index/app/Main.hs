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
import           Data.Maybe                        (maybeToList)
import           Data.Proxy                        (Proxy (..))
import           Data.Sequence                     (Seq, (<|))
import           Data.Text.Prettyprint.Doc         (Pretty (..))
import qualified Data.Yaml                         as Y
import qualified Database.Beam                     as Beam
import qualified Database.Beam.Migrate.Simple      as Beam
import qualified Database.Beam.Sqlite              as Sqlite
import qualified Database.Beam.Sqlite.Migrate      as Sqlite
import qualified Database.SQLite.Simple            as Sqlite
import           Options.Applicative               (execParser)
import qualified Plutus.ChainIndex.Server          as Server

import           Cardano.Api                       (ChainPoint (..), deserialiseFromRawBytes, proxyToAsType)
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
import           Plutus.ChainIndex.DbStore         (DbStoreEffect, TipRowT (..), checkedSqliteDb, db, handleDbStore,
                                                    tipRow)
import           Plutus.ChainIndex.Effects         (ChainIndexControlEffect (..), ChainIndexQueryEffect (..),
                                                    appendBlock, rollback)
import           Plutus.ChainIndex.Handlers        (ChainIndexState, fromByteString, handleControl, handleQuery)
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
  -> IO ()
runChainIndex trace emulatorState conn effect = do
  -- First run the STM block capturing all log messages emited on a
  -- successful STM transaction.
  oldEmulatorState <- STM.atomically $ STM.readTVar emulatorState
  (result, logMessages') <-
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
  logMessages <- case result of
      Left err ->
        pure $ LogMessage Error (Err err) <| logMessages'
      Right (_, newState) -> do
        STM.atomically $ STM.writeTVar emulatorState newState
        pure logMessages'
  -- Log all previously captured messages
  traverse_ (send . LMessage) logMessages
    & runLogEffects trace

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
        runChainIndex trace mState conn $ appendBlock (tipFromCardanoBlock block) txs
chainSyncHandler trace mState conn
  (RollBackward point _) _ = do
    -- Do we really want to pass the tip of the new blockchain to the
    -- rollback function (rather than the point where the chains diverge)?
    runChainIndex trace mState conn $ rollback (fromCardanoPoint point)
-- On resume we do nothing, for now.
chainSyncHandler _ _ _ (Resume _) _ = do
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

      Sqlite.withConnection (Config.cicDbPath config) $ \conn -> do
        resumePoints <- Sqlite.runBeamSqliteDebug (logDebug trace . SqlLog) conn $ do
          -- Migrate DB first
          Beam.autoMigrate Sqlite.migrationBackend checkedSqliteDb

          -- Get the current tip to sync from there
          tip <- Beam.runSelectReturningOne $ Beam.select $ Beam.all_ (tipRow db)
          pure $ maybeToList $ do
            TipRow _ s bid _ <- tip
            hash <- deserialiseFromRawBytes (proxyToAsType Proxy) bid
            pure (ChainPoint (fromByteString s) hash)

        putStrLn $ "Connecting to the node using socket: " <> Config.cicSocketPath config
        putStrLn $ case resumePoints of
          [ChainPoint s _] -> "Continue to sync from: " <> show s
          _                -> "Syncing from genesis"
        void $ runChainSync (Config.cicSocketPath config)
                            nullTracer
                            (Config.cicSlotConfig config)
                            (Config.cicNetworkId  config)
                            resumePoints
                            (chainSyncHandler trace appState conn)

        putStrLn $ "Starting webserver on port " <> show (Config.cicPort config)
        Server.serveChainIndexQueryServer (Config.cicPort config) trace appState conn
