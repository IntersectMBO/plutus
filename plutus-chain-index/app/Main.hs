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

import qualified Control.Concurrent.STM          as STM
import           Control.Exception               (throwIO)
import           Control.Monad.Freer             (Eff, send)
import           Control.Monad.Freer.Extras      (LogMsg (..))
import           Control.Monad.Freer.Extras.Beam (BeamEffect, BeamLog (..))
import           Control.Monad.Freer.Extras.Log  (LogLevel (..), LogMessage (..))
import           Control.Tracer                  (nullTracer)
import qualified Data.Aeson                      as A
import           Data.Foldable                   (for_, traverse_)
import           Data.Function                   ((&))
import           Data.Functor                    (void)
import           Data.Sequence                   ((<|))
import           Data.Text.Prettyprint.Doc       (Pretty (..))
import qualified Data.Yaml                       as Y
import           Database.Beam.Migrate.Simple    (autoMigrate)
import qualified Database.Beam.Sqlite            as Sqlite
import qualified Database.Beam.Sqlite.Migrate    as Sqlite
import qualified Database.SQLite.Simple          as Sqlite
import           Options.Applicative             (execParser)

import qualified Cardano.BM.Configuration.Model  as CM
import           Cardano.BM.Setup                (setupTrace_)
import           Cardano.BM.Trace                (Trace, logDebug, logError)

import           Cardano.Api                     (ChainPoint)
import           Cardano.Protocol.Socket.Client  (ChainSyncEvent (..), runChainSync)
import           CommandLine                     (AppConfig (..), Command (..), applyOverrides, cmdWithHelpParser)
import qualified Config
import           Ledger                          (Slot (..))
import qualified Logging
import           Plutus.ChainIndex               (ChainIndexLog (..), RunRequirements (..), runChainIndexEffects)
import           Plutus.ChainIndex.Compatibility (fromCardanoBlock, fromCardanoPoint, tipFromCardanoBlock)
import           Plutus.ChainIndex.DbSchema      (checkedSqliteDb)
import           Plutus.ChainIndex.Effects       (ChainIndexControlEffect (..), ChainIndexQueryEffect (..), appendBlock,
                                                  resumeSync, rollback)
import           Plutus.ChainIndex.Handlers      (getResumePoints)
import qualified Plutus.ChainIndex.Server        as Server
import           Plutus.ChainIndex.Types         (pointSlot)
import           Plutus.Monitoring.Util          (runLogEffects)


runChainIndex
  :: RunRequirements
  -> Eff '[ChainIndexQueryEffect, ChainIndexControlEffect, BeamEffect] a
  -> IO (Maybe a)
runChainIndex runReq effect = do
  (errOrResult, logMessages') <- runChainIndexEffects runReq effect
  (result, logMessages) <- case errOrResult of
      Left err ->
        pure (Nothing, LogMessage Error (Err err) <| logMessages')
      Right result -> do
        pure (Just result, logMessages')
  -- Log all previously captured messages
  traverse_ (send . LMessage) logMessages
    & runLogEffects (trace runReq)
  pure result

chainSyncHandler
  :: RunRequirements
  -> ChainSyncEvent
  -> Slot
  -> IO ()
chainSyncHandler runReq
  (RollForward block _) _ = do
    let ciBlock = fromCardanoBlock block
    case ciBlock of
      Left err    ->
        logError (trace runReq) (ConversionFailed err)
      Right txs ->
        void $ runChainIndex runReq $ appendBlock (tipFromCardanoBlock block) txs
chainSyncHandler runReq
  (RollBackward point _) _ = do
    putStr "Rolling back to "
    print point
    -- Do we really want to pass the tip of the new blockchain to the
    -- rollback function (rather than the point where the chains diverge)?
    void $ runChainIndex runReq $ rollback (fromCardanoPoint point)
chainSyncHandler runReq
  (Resume point) _ = do
    putStr "Resuming from "
    print point
    void $ runChainIndex runReq $ resumeSync $ fromCardanoPoint point

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
        Sqlite.execute_ conn
          "CREATE TRIGGER delete_matching_input AFTER DELETE ON unspent_outputs \
          \BEGIN \
          \  DELETE FROM unmatched_inputs WHERE input_row_tip__row_slot = old.output_row_tip__row_slot \
          \                                 AND input_row_out_ref = old.output_row_out_ref; \
          \END"

        stateTVar <- STM.newTVarIO mempty
        let runReq = RunRequirements trace stateTVar conn (Config.cicSecurityParam config)

        Just resumePoints <- runChainIndex runReq getResumePoints

        putStr "\nPossible resume slots: "
        putStrLn $ showResumePoints resumePoints

        putStrLn $ "Connecting to the node using socket: " <> Config.cicSocketPath config
        void $ runChainSync (Config.cicSocketPath config)
                            nullTracer
                            (Config.cicSlotConfig config)
                            (Config.cicNetworkId  config)
                            resumePoints
                            (chainSyncHandler runReq)

        putStrLn $ "Starting webserver on port " <> show (Config.cicPort config)
        Server.serveChainIndexQueryServer (Config.cicPort config) runReq
