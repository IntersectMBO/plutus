-- editorconfig-checker-disable-file

{-# LANGUAGE DeriveAnyClass   #-}
{-# LANGUAGE LambdaCase       #-}
{-# LANGUAGE RecordWildCards  #-}
{-# LANGUAGE TupleSections    #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -fno-warn-unused-imports #-}
{-# OPTIONS_GHC -fno-warn-unused-matches #-}
{-# OPTIONS_GHC -fno-warn-unused-top-binds #-}

-- TODO: restore warnings once this is finalised.

module Main (main) where

import PlutusCore.Data qualified as PLC
import PlutusCore.Pretty
import PlutusLedgerApi.Common
import PlutusLedgerApi.Test.EvaluationEvent
import PlutusLedgerApi.V1 qualified as V1
import PlutusLedgerApi.V2 qualified as V2

import PlutusLedgerApi.V1.Contexts qualified as V1
import PlutusLedgerApi.V2.Contexts qualified as V2

import PlutusTx.AssocMap qualified as M

import Codec.Serialise (Serialise, readFileDeserialise)
import Control.Concurrent.Async (mapConcurrently)
import Control.Exception (evaluate)
import Control.Monad.Extra (whenJust)
import Control.Monad.Writer.Strict
import Data.List (intercalate)
import Data.List.NonEmpty (NonEmpty, nonEmpty, toList)
import Data.Maybe (catMaybes)
import GHC.Generics (Generic)
import System.Directory.Extra (listFiles)
import System.Environment (getEnv)
import System.FilePath (isExtensionOf, takeBaseName)
import System.IO (hFlush, stdout)
import System.IO.Unsafe
import Text.Printf (printf)

{- The ScriptEvaluationData type used to contain a ProtocolVersion but now
 contains only a MajorProtocolVersion.  The program which dumps the mainnet
 scripts still writes both the major and minor protocol version numbers, so here
 we provide some adaptor types which allow us to read the old format and convert
 it to the new format.  We expect that this program will be subsumed by Marconi
 eventually, so we just go for a quick fix here for the time being instead of
 rewriting the script-dumper; also this strategy allows us to process existing
 files without having to re-dump all of the scripts from the history of the
 chain.
-}

-- Adaptor types

data ProtocolVersion = ProtocolVersion
    { pvMajor :: Int -- ^ the major component
    , pvMinor :: Int -- ^ the minor component
    }
    deriving stock (Show, Eq, Generic)
    deriving anyclass Serialise

data ScriptEvaluationData2 = ScriptEvaluationData2
    { dataProtocolVersion2 :: ProtocolVersion
    , dataBudget2          :: ExBudget
    , dataScript2          :: SerialisedScript
    , dataInputs2          :: [PLC.Data]
    }
    deriving stock (Show, Generic)
    deriving anyclass (Serialise)

data ScriptEvaluationEvent2
    = PlutusV1Event2 ScriptEvaluationData2 ScriptEvaluationResult
    | PlutusV2Event2 ScriptEvaluationData2 ScriptEvaluationResult
    deriving stock (Show, Generic)
    deriving anyclass (Serialise)

data ScriptEvaluationEvents2 = ScriptEvaluationEvents2
    { eventsCostParamsV1' :: Maybe [Integer]
    -- ^ Cost parameters shared by all PlutusV1 evaluation events in `eventsEvents`, if any.
    , eventsCostParamsV2' :: Maybe [Integer]
    -- ^ Cost parameters shared by all PlutusV2 evaluation events in `eventsEvents`, if any.
    , eventsEvents2       :: NonEmpty ScriptEvaluationEvent2
    }
    deriving stock (Show, Generic)
    deriving anyclass Serialise

-- Conversion functions

data2toData :: ScriptEvaluationData2 -> ScriptEvaluationData
data2toData (ScriptEvaluationData2 (ProtocolVersion v _)  b s i) =
    ScriptEvaluationData (MajorProtocolVersion v) b s i

event2toEvent :: ScriptEvaluationEvent2 -> ScriptEvaluationEvent
event2toEvent (PlutusV1Event2 d r) = PlutusV1Event (data2toData d) r
event2toEvent (PlutusV2Event2 d r) = PlutusV2Event (data2toData d) r

events2toEvents :: ScriptEvaluationEvents2 -> ScriptEvaluationEvents
events2toEvents (ScriptEvaluationEvents2 cpV1 cpV2 evs) =
    ScriptEvaluationEvents cpV1 cpV2 (fmap event2toEvent evs)

-- Transaction analysis

-- Minting policy: redeemer, context
-- Validator: datum, redeemer, context

analyseEvaluationEvent ::
    EvaluationContext ->
    -- | Cost parameters
    [Integer] ->
    ScriptEvaluationEvent ->
    IO (Maybe UnexpectedEvaluationResult)
analyseEvaluationEvent ctx params ev = case ev of
    PlutusV1Event ScriptEvaluationData{..} expected ->
        case deserialiseScript PlutusV1 dataProtocolVersion dataScript of
            Right script ->
                let (_, actual) =
                        V1.evaluateScriptRestricting
                            dataProtocolVersion
                            V1.Quiet
                            ctx
                            dataBudget
                            script
                            dataInputs
                 in verify expected actual
            Left err -> pure $ Just (DecodeError err)
    PlutusV2Event ScriptEvaluationData{..} expected ->
        case deserialiseScript PlutusV2 dataProtocolVersion dataScript of
            Right script ->
                let (_, actual) =
                        V2.evaluateScriptRestricting
                            dataProtocolVersion
                            V2.Quiet
                            ctx
                            dataBudget
                            script
                            dataInputs
                 in verify expected actual
            Left err -> pure $ Just (DecodeError err)
  where
    verify ScriptEvaluationSuccess (Left err) =
        pure $ Just $ UnexpectedEvaluationFailure ev params err
    verify ScriptEvaluationFailure (Right budget) =
        pure $ Just $ UnexpectedEvaluationSuccess ev params budget
    verify _ _ = pure Nothing

stringOfPurpose :: V1.ScriptPurpose -> String
stringOfPurpose = \case
    V1.Minting    _ -> "Minting"
    V1.Spending   _ -> "Spending"
    V1.Rewarding  _ -> "Rewarding"
    V1.Certifying _ -> "Certifying"


-- Analyse values in ScriptContext

shapeOfValue :: V1.Value  -> String
shapeOfValue (V1.Value m) =
    let l = M.toList m
    in printf "[%d: %s]" (length l) (intercalate "," (fmap (printf "%d" . length . M.toList . snd) l))

analyseValue :: V1.Value -> IO ()
analyseValue v = do
  putStr $ shapeOfValue v
  putStr $ printf "\n"

analyseOutputsV1 :: [V1.TxOut] -> IO ()
analyseOutputsV1 l = do
    putStr $ printf " %d " (length l)
    putStrLn $ intercalate ", " (fmap (shapeOfValue . V1.txOutValue) l)

analyseTxInfoV1 :: V1.TxInfo -> IO ()
analyseTxInfoV1 i = do
  putStr "Fee:     "
  analyseValue $ V1.txInfoFee i
  putStr "Mint:    "
  analyseValue $ V1.txInfoMint i
--  putStrLn $ show $ V1.txInfoMint i
  putStr "Outputs: "
  analyseOutputsV1 $ V1.txInfoOutputs i

analyseOutputsV2 :: [V2.TxOut] -> IO ()
analyseOutputsV2 l = do
    putStr $ printf " %d " (length l)
    putStrLn $ intercalate ", " (fmap (shapeOfValue . V2.txOutValue ) l)

analyseTxInfoV2 :: V2.TxInfo -> IO ()
analyseTxInfoV2 i = do
  putStr "Fee:     "
  analyseValue $ V2.txInfoFee i
  putStr "Mint:    "
  analyseValue $ V2.txInfoMint i
--  putStrLn $ show $ V2.txInfoMint i
  putStr "Outputs: "
  analyseOutputsV2 $ V2.txInfoOutputs i

analyseScriptContext ::
    EvaluationContext ->
    -- | Cost parameters
    [Integer] ->
    ScriptEvaluationEvent ->
    IO (Maybe UnexpectedEvaluationResult)
analyseScriptContext _ctx _params ev = case ev of
    PlutusV1Event ScriptEvaluationData{..} _expected ->
        case dataInputs of
        [_,_,c] -> analyseCtxV1 c
        [_,c]   -> analyseCtxV1 c
        _       -> pure Nothing
    PlutusV2Event ScriptEvaluationData{..} _expected ->
        case dataInputs of
        [_,_,c] -> analyseCtxV2 c
        [_,c]   -> analyseCtxV2 c
        _       -> pure Nothing
    where
    analyseCtxV1 c = case V1.fromData @V1.ScriptContext c of
                       Nothing -> pure Nothing -- pure . Just . DecodeError $ LedgerLanguageNotAvailableError
                       Just p -> do
                         putStrLn "----------------"
                         putStrLn $ stringOfPurpose $ V1.scriptContextPurpose p
                         analyseTxInfoV1 $ V1.scriptContextTxInfo p
                         pure Nothing
    analyseCtxV2 c = case V2.fromData @V2.ScriptContext c of
                       Nothing -> pure Nothing -- pure . Just . DecodeError $ LedgerLanguageNotAvailableError
                       Just p -> do
                         putStrLn "----------------"
                         putStrLn $ stringOfPurpose $ V2.scriptContextPurpose p
                         analyseTxInfoV2 $ V2.scriptContextTxInfo p
                         pure Nothing


-- Redeemer analysis


-- | Test cases from a single event dump file
analyseOneFile :: FilePath -> IO ()
analyseOneFile eventFile = do
  events <- events2toEvents <$> readFileDeserialise @ScriptEvaluationEvents2 eventFile

  case ( mkContext V1.mkEvaluationContext (eventsCostParamsV1 events)
       , mkContext V2.mkEvaluationContext (eventsCostParamsV2 events)
       ) of
    (Right ctxV1, Right ctxV2) ->
        do
          errs <-
              fmap catMaybes $
              mapM
              (evaluate . runSingleEvent ctxV1 ctxV2)
              (toList (eventsEvents events))
          whenJust (nonEmpty errs) $ error . renderTestFailures
    (Left err, _) -> error $ display err
    (_, Left err) -> error $ display err
  where
    mkContext f = \case
        Nothing         -> Right Nothing
        Just costParams -> Just . (,costParams) . fst <$> runWriterT (f costParams)

    runSingleEvent
        :: Maybe (EvaluationContext, [Integer])
        -> Maybe (EvaluationContext, [Integer])
        -> ScriptEvaluationEvent
        -> Maybe TestFailure
    runSingleEvent ctxV1 ctxV2 event =
        case event of
            PlutusV1Event{} -> case ctxV1 of
                                 Just (ctx, params) ->
                                            InvalidResult <$> (unsafePerformIO $ analyseScriptContext ctx params event)
                                 Nothing            -> Just $ MissingCostParametersFor PlutusV1
            PlutusV2Event{} -> case ctxV2 of
                                 Just (ctx, params) ->
                                            InvalidResult <$> (unsafePerformIO $ analyseScriptContext ctx params event)
                                 Nothing            -> Just $ MissingCostParametersFor PlutusV2

main :: IO ()
main = do
    dir <- getEnv "EVENT_DUMP_DIR"
    eventFiles <- filter ("event" `isExtensionOf`) <$> listFiles dir
    mapM_ analyseOneFile eventFiles
