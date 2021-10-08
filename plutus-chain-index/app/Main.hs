{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE DeriveAnyClass      #-}
{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE DerivingStrategies  #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE NamedFieldPuns      #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}

module Main where

import qualified Control.Concurrent.STM            as STM
import           Control.Exception                 (throwIO)
import           Control.Lens                      (unto)
import           Control.Monad.Freer               (Eff, interpret, reinterpret, runM, send)
import           Control.Monad.Freer.Error         (Error, handleError, runError, throwError)
import           Control.Monad.Freer.Extras        (LogMsg (..))
import           Control.Monad.Freer.Extras.Log    (LogLevel (..), LogMessage (..), handleLogWriter)
import           Control.Monad.Freer.Reader        (Reader, runReader)
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

import           Cardano.Api                       (ChainPoint)
import           Cardano.Protocol.Socket.Client    (ChainSyncEvent (..), runChainSync)
import           CommandLine                       (AppConfig (..), Command (..), applyOverrides, cmdWithHelpParser)
import qualified Config
import           Control.Monad.Freer.Extras.Beam   (BeamEffect, BeamError (..), BeamLog (..), handleBeam)
import           Ledger                            (Slot (..))
import qualified Logging
import           Plutus.ChainIndex.ChainIndexError (ChainIndexError (..))
import           Plutus.ChainIndex.ChainIndexLog   (ChainIndexLog (..))
import           Plutus.ChainIndex.Compatibility   (fromCardanoBlock, fromCardanoPoint, tipFromCardanoBlock)
import           Plutus.ChainIndex.DbSchema        (checkedSqliteDb)
import           Plutus.ChainIndex.Effects         (ChainIndexControlEffect (..), ChainIndexQueryEffect (..),
                                                    appendBlock, rollback)
import           Plutus.ChainIndex.Handlers        (ChainIndexState, getResumePoints, handleControl, handleQuery,
                                                    restoreStateFromDb)
import           Plutus.ChainIndex.Types           (pointSlot)
import           Plutus.Monitoring.Util            (convertLog, runLogEffects)


type ChainIndexEffects
  = '[ ChainIndexControlEffect
     , ChainIndexQueryEffect
     , BeamEffect
     , Reader Sqlite.Connection
     , Error BeamError
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
  -> IO (Maybe a)
runChainIndex trace mState conn effect = do
  -- First run the STM block capturing all log messages emited on a
  -- successful STM transaction.
  oldEmulatorState <- STM.atomically $ STM.readTVar mState
  (errOrResult, logMessages') <-
    effect
    & interpret handleControl
    & interpret handleQuery
    & interpret (handleBeam (convertLog BeamLogItem trace))
    & runReader conn
    & flip handleError (throwError . BeamEffectError)
    & runState oldEmulatorState
    & runError
    & reinterpret
        (handleLogWriter @ChainIndexLog
                          @(Seq (LogMessage ChainIndexLog)) $ unto pure)
    & runWriter @(Seq (LogMessage ChainIndexLog))
    & runM
  (result, logMessages) <- case errOrResult of
      Left err ->
        pure (Nothing, LogMessage Error (Err err) <| logMessages')
      Right (result, newState) -> do
        STM.atomically $ STM.writeTVar mState newState
        pure (Just result, logMessages')
  -- Log all previously captured messages
  traverse_ (send . LMessage) logMessages
    & runLogEffects trace
  pure result

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
    void $ runChainIndex trace mState conn $ restoreStateFromDb $ fromCardanoPoint point

showResumePoints :: [ChainPoint] -> String
showResumePoints = \case
  []  -> "none"
  [x] -> showPoint x
  xs  -> showPoint (head xs) ++ ", " ++ showPoint (xs !! 1) ++ " .. " ++ showPoint (last xs)
  where
    showPoint = show . toInteger . pointSlot . fromCardanoPoint


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

        -- Optimize Sqlite for write performance, halves the sync time.
        -- https://sqlite.org/wal.html
        Sqlite.execute_ conn "PRAGMA journal_mode=WAL"
        Sqlite.runBeamSqliteDebug (logDebug trace . (BeamLogItem . SqlLog)) conn $ do
          autoMigrate Sqlite.migrationBackend checkedSqliteDb

        -- Automatically delete the input when an output from a matching input/output pair is deleted.
        -- See reduceOldUtxoDb in Plutus.ChainIndex.Handlers
        Sqlite.execute_ conn "DROP TRIGGER IF EXISTS delete_matching_input"
        Sqlite.execute_ conn $
          "CREATE TRIGGER delete_matching_input AFTER DELETE ON unspent_outputs \
          \BEGIN \
          \  DELETE FROM unmatched_inputs WHERE input_row_tip__row_slot = old.output_row_tip__row_slot \
          \                                 AND input_row_out_ref = old.output_row_out_ref; \
          \END"

        appState <- STM.newTVarIO mempty
        Just resumePoints <- runChainIndex trace appState conn getResumePoints

        putStr "\nPossible resume slots: "
        putStrLn $ showResumePoints resumePoints

        putStrLn $ "Connecting to the node using socket: " <> Config.cicSocketPath config
        void $ runChainSync (Config.cicSocketPath config)
                            nullTracer
                            (Config.cicSlotConfig config)
                            (Config.cicNetworkId  config)
                            resumePoints
                            (chainSyncHandler trace appState conn)

        putStrLn $ "Starting webserver on port " <> show (Config.cicPort config)
        Server.serveChainIndexQueryServer (Config.cicPort config) trace appState conn
