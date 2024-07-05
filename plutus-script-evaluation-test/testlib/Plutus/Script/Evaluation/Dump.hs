-- editorconfig-checker-disable-file

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes       #-}

module Plutus.Script.Evaluation.Dump
  ( dumpScriptEvents,
  )
where

import Cardano.Api qualified as Cardano
import Cardano.Ledger.Alonzo.Scripts (getCostModelParams)
import Cardano.Ledger.Alonzo.TxInfo qualified as Alonzo
import Cardano.Ledger.BaseTypes qualified as Ledger
import Cardano.Streaming (ChainSyncEventException (NoIntersectionFound), foldLedgerStateEvents,
                          singletonLedgerStateHistory, withChainSyncEventStream)
import Codec.Serialise qualified as CBOR
import Control.Applicative (Alternative ((<|>)))
import Control.Exception (fromException, handle, throwIO)
import Control.Monad.Extra (when, whenJust)
import Control.Monad.Trans.Except (runExceptT)
import Control.Monad.Trans.State (evalStateT, get, put)
import Data.ByteString.Base16 qualified as B16
import Data.Foldable (traverse_)
import Data.List (sortBy)
import Data.List.NonEmpty qualified as NonEmpty
import Data.Map qualified as M
import Data.Maybe (fromMaybe)
import Data.Text qualified as Text
import Data.Text.Encoding qualified as Text
import Data.Word (Word64)
import Plutus.ApiCommon (ProtocolVersion (ProtocolVersion))
import Plutus.Script.Evaluation.Options qualified as O
import Plutus.Script.Evaluation.Types (Block, Checkpoint (Checkpoint), ScriptM,
                                       StreamerState (StreamerState, ssCount, ssEvents, ssV1CostParams, ssV2CostParams))
import PlutusLedgerApi.Test.EvaluationEvent (ScriptEvaluationData (ScriptEvaluationData),
                                             ScriptEvaluationEvent (PlutusV1Event, PlutusV2Event),
                                             ScriptEvaluationEvents (ScriptEvaluationEvents, eventsCostParamsV1, eventsCostParamsV2, eventsEvents),
                                             ScriptEvaluationResult (ScriptEvaluationFailure, ScriptEvaluationSuccess))
import PyF (fmt)
import Streaming (MFunctor (hoist), MonadIO (liftIO), Of, Stream)
import Streaming.Prelude qualified as S
import System.Directory.Extra (listFiles, removeFile)
import System.Environment (getEnv)
import System.FilePath (isExtensionOf, takeBaseName, (<.>), (</>))
import System.IO (hPrint, hPutStrLn, stderr)
import System.IO.Error (isDoesNotExistError)
import System.Process.Extra (system_)
import System.Time.Extra (sleep)
import Text.Printf (printf)

-- | Stream blocks from a local node, and periodically dump ledger events
-- and checkpoint ledger state.
dumpScriptEvents :: O.Options -> IO ()
dumpScriptEvents opts = do
  (env, ledgerStateAtGenesis) <-
    either (fail . Text.unpack . Cardano.renderInitialLedgerStateError) pure
      =<< runExceptT (Cardano.initialLedgerState (O.optsConfigPath opts))
  dumpDir <- getEnv "DUMP_DIR"
  checkpointDir <- getEnv "CHECKPOINT_DIR"
  let onDeserialiseFailure :: [FilePath] -> CBOR.DeserialiseFailure -> IO ()
      onDeserialiseFailure fps e = case fps of
        [] -> throwIO e
        (_ : rest) -> do
          putStrLn $ "Deserialise failure: " <> show e
          go rest
      go :: [FilePath] -> IO ()
      go fps = handle (onDeserialiseFailure fps) $ do
        (chainPoint, ledgerState, onApplyBlockException) <- case fps of
          -- No checkpoint to use, so start from Genesis.
          [] -> pure (Cardano.ChainPointAtGenesis, ledgerStateAtGenesis, throwIO)
          -- Try the latest checkpoint, and if we get an `ApplyBlockException` (which likely
          -- means the checkpointed block was rolled back), try the next one.
          latestStateFile : rest -> do
            putStrLn $ "Reading ledger state from " <> latestStateFile
            Checkpoint chainPoint ledgerState <- CBOR.readFileDeserialise latestStateFile
            cleanupStateAndEventFiles dumpDir latestStateFile
            cleanupStateAndEventFiles checkpointDir latestStateFile
            putStrLn
              [fmt|
Starting from checkpoint in {latestStateFile}
  slot: {maybe "Genesis" show (Cardano.chainPointToSlotNo chainPoint)}
  hash: {maybe "Genesis" renderBlockHash (Cardano.chainPointToHeaderHash chainPoint)}
|]
            pure (chainPoint, ledgerState, \(e :: Cardano.LedgerStateError) -> hPrint stderr e >> go rest)

        let -- Handles socket does not exist exception and no intersection found exception
            handler e
              | Just ioerror <- fromException e,
                isDoesNotExistError ioerror = do
                  hPutStrLn stderr "Node socket does not exist. Retrying in 30s"
                  sleep 30
                  startStreaming
              | Just NoIntersectionFound <- fromException e = do
                  hPutStrLn
                    stderr
                    "No intersection found - perhaps the node is behind. Retrying in 30s"
                  sleep 30
                  startStreaming
              | otherwise = throwIO e

            startStreaming = handle onApplyBlockException
              . handle handler
              . withChainSyncEventStream
                (O.optsSocketPath opts)
                (O.optsNetworkId opts)
                [chainPoint]
              $ \blockStream -> do
                let eventStream ::
                      Stream
                        (Of (Block, (Cardano.LedgerState, [Cardano.LedgerEvent])))
                        ScriptM
                        ()
                    eventStream =
                      hoist liftIO $
                        foldLedgerStateEvents env (singletonLedgerStateHistory ledgerState) Cardano.FullValidation blockStream
                flip evalStateT (StreamerState 0 Nothing Nothing []) $
                  runStream dumpDir checkpointDir (O.optsBlocksPerFile opts) (O.optsEventsPerFile opts) eventStream
        startStreaming

  liftIO $ system_ "./scripts/s3-sync-checkpoint.sh"
  go =<< listStateFiles checkpointDir

runStream ::
  forall r.
  FilePath ->
  FilePath ->
  -- | Blocks per file
  Word64 ->
  -- | Events per file
  Word64 ->
  Stream
    (Of (Block, (Cardano.LedgerState, [Cardano.LedgerEvent])))
    ScriptM
    r ->
  ScriptM r
runStream dumpDir checkpointDir blocksPerFile eventsPerFile stream = do
  S.mapM_ (uncurry (uncurry . checkpoint)) stream
  where
    checkpoint :: Block -> Cardano.LedgerState -> [Cardano.LedgerEvent] -> ScriptM ()
    checkpoint block ledgerState ledgerEvents = do
      streamerState <- get
      let currentV1CostParams = ssV1CostParams streamerState
          currentV2CostParams = ssV2CostParams streamerState
          (newScriptEvents, newV1CostParams, newV2CostParams) = toScriptEvents ledgerEvents
      when (ssCount streamerState `mod` 1000 == 0) . liftIO $
        putStrLn $
          "blocks processed: " <> show (ssCount streamerState)
      if ssCount streamerState >= blocksPerFile
        || fromIntegral (length (ssEvents streamerState)) >= eventsPerFile
        || changed currentV1CostParams newV1CostParams
        || changed currentV2CostParams newV2CostParams
        then do
          liftIO $ putStrLn "Creating new checkpoint"
          let chainPoint = blockChainPoint block
              slot = Cardano.chainPointToSlotNo chainPoint
              hash = Cardano.chainPointToHeaderHash chainPoint
          let filePrefix =
                printf "%016d" (maybe 0 Cardano.unSlotNo slot)
                  <> "-"
                  <> maybe "Genesis" (Text.unpack . renderBlockHash) hash
              eventFile = dumpDir </> filePrefix <.> eventsFileExt
          whenJust (NonEmpty.nonEmpty (ssEvents streamerState)) $ \evs -> do
            let scriptEvents =
                  ScriptEvaluationEvents
                    { eventsCostParamsV1 = currentV1CostParams,
                      eventsCostParamsV2 = currentV2CostParams,
                      eventsEvents = evs
                    }
            liftIO $ CBOR.writeFileSerialise eventFile scriptEvents
          liftIO . system_ $ "./scripts/upload-event-dump.sh " <> eventFile
          -- Writing state (checkpoint) file after everything else ensures the events of a
          -- checkpoint are persisted in S3.
          let stateFile = checkpointDir </> filePrefix <.> stateFileExt

          liftIO $ CBOR.writeFileSerialise stateFile (Checkpoint chainPoint ledgerState)
          put $ StreamerState 0 newV1CostParams newV2CostParams []
          liftIO $
            putStrLn
              [fmt|
Created new checkpoint in {stateFile}
  number of blocks: {ssCount streamerState}
  number of script evaluation events: {length (ssEvents streamerState)}
  slot: {maybe "Genesis" show slot}
  hash: {maybe "Genesis" renderBlockHash hash}
|]
        else do
          put $
            streamerState
              { ssEvents = newScriptEvents ++ ssEvents streamerState,
                ssV1CostParams = currentV1CostParams <|> newV1CostParams,
                ssV2CostParams = currentV2CostParams <|> newV2CostParams,
                ssCount = ssCount streamerState + 1
              }

changed :: Maybe [Integer] -> Maybe [Integer] -> Bool
changed params1 params2 = fromMaybe False $ (/=) <$> params1 <*> params2

stateFileExt, eventsFileExt :: String
stateFileExt = "state"
eventsFileExt = "event"

blockChainPoint :: Block -> Cardano.ChainPoint
blockChainPoint (Cardano.BlockInMode (Cardano.Block (Cardano.BlockHeader slot hash _) _) _) =
  Cardano.ChainPoint slot hash

toScriptEvents :: [Cardano.LedgerEvent] -> ([ScriptEvaluationEvent], Maybe [Integer], Maybe [Integer])
toScriptEvents = foldr alg ([], Nothing, Nothing)
  where
    alg ::
      Cardano.LedgerEvent ->
      ([ScriptEvaluationEvent], Maybe [Integer], Maybe [Integer]) ->
      ([ScriptEvaluationEvent], Maybe [Integer], Maybe [Integer])
    alg ledgerEvent acc = case ledgerEvent of
      Cardano.SuccessfulPlutusScript ds -> foldr (alg' ScriptEvaluationSuccess) acc ds
      Cardano.FailedPlutusScript ds     -> foldr (alg' ScriptEvaluationFailure) acc ds
      _                                 -> acc

    alg' ::
      ScriptEvaluationResult ->
      Alonzo.PlutusDebug ->
      ([ScriptEvaluationEvent], Maybe [Integer], Maybe [Integer]) ->
      ([ScriptEvaluationEvent], Maybe [Integer], Maybe [Integer])
    alg' res d (scriptEvents, v1, v2) = case d of
      Alonzo.PlutusDebugV1 costModel units script inputs (Ledger.ProtVer major minor) ->
        let params = M.elems (getCostModelParams costModel)
            budget = Alonzo.transExUnits units
            ver = ProtocolVersion (fromIntegral major) (fromIntegral minor)
            evaluationData = ScriptEvaluationData ver budget script inputs
         in (PlutusV1Event evaluationData res : scriptEvents, v1 <|> Just params, v2)
      Alonzo.PlutusDebugV2 costModel units script inputs (Ledger.ProtVer major minor) ->
        let params = M.elems (getCostModelParams costModel)
            budget = Alonzo.transExUnits units
            ver = ProtocolVersion (fromIntegral major) (fromIntegral minor)
            evaluationData = ScriptEvaluationData ver budget script inputs
         in (PlutusV2Event evaluationData res : scriptEvents, v1, v2 <|> Just params)

listStateFiles :: FilePath -> IO [FilePath]
listStateFiles =
  fmap (sortBy (flip compare) . filter (stateFileExt `isExtensionOf`)) . listFiles

-- | Remove the state and event files whose timestamps are greater than the given state file
cleanupStateAndEventFiles :: FilePath -> FilePath -> IO ()
cleanupStateAndEventFiles dir stateFile = do
  newerStateAndEventFiles <-
    takeWhile (\f -> takeBaseName f > takeBaseName stateFile)
      . sortBy (flip compare)
      . filter (\f -> stateFileExt `isExtensionOf` f || eventsFileExt `isExtensionOf` f)
      <$> listFiles dir
  traverse_ removeFile newerStateAndEventFiles

renderBlockHash :: Cardano.Hash Cardano.BlockHeader -> Text.Text
renderBlockHash = Text.decodeLatin1 . B16.encode . Cardano.serialiseToRawBytes
