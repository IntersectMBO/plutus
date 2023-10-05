{-# LANGUAGE DeriveAnyClass   #-}
{-# LANGUAGE LambdaCase       #-}
{-# LANGUAGE TupleSections    #-}
{-# LANGUAGE TypeApplications #-}

module Main (main) where

import PlutusCore.Data qualified as PLC
import PlutusCore.Pretty
import PlutusLedgerApi.Common
import PlutusLedgerApi.Test.EvaluationEvent
import PlutusLedgerApi.V1 qualified as V1
import PlutusLedgerApi.V2 qualified as V2

import Codec.Serialise (Serialise, readFileDeserialise)
import Control.Concurrent.Async (mapConcurrently)
import Control.Exception (evaluate)
import Control.Monad.Extra (whenJust)
import Control.Monad.Writer.Strict
import Data.List.NonEmpty (NonEmpty, nonEmpty, toList)
import Data.Maybe (catMaybes)
import GHC.Generics (Generic)
import System.Directory.Extra (listFiles)
import System.Environment (getEnv)
import System.FilePath (isExtensionOf, takeBaseName)
import Test.Tasty
import Test.Tasty.HUnit

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

-- Back to business as usual

-- | Test cases from a single event dump file
testOneFile :: FilePath -> TestTree
testOneFile eventFile = testCase (takeBaseName eventFile) $ do
    events <- events2toEvents <$> readFileDeserialise @ScriptEvaluationEvents2 eventFile

    case ( mkContext V1.mkEvaluationContext (eventsCostParamsV1 events)
         , mkContext V2.mkEvaluationContext (eventsCostParamsV2 events)
         ) of
        (Right ctxV1, Right ctxV2) -> do
            errs <-
                fmap catMaybes $
                    mapConcurrently
                        (evaluate . runSingleEvent ctxV1 ctxV2)
                        (toList (eventsEvents events))
            whenJust (nonEmpty errs) $ assertFailure . renderTestFailures
        (Left err, _) -> assertFailure $ display err
        (_, Left err) -> assertFailure $ display err
  where
    mkContext f = \case
        Nothing         -> Right Nothing
        Just costParams -> Just . (,costParams) . fst <$> runWriterT (f costParams)

    runSingleEvent ctxV1 ctxV2 event =
        case event of
            PlutusV1Event{} -> case ctxV1 of
                Just (ctx, params) -> InvalidResult <$> checkEvaluationEvent ctx params event
                Nothing            -> Just $ MissingCostParametersFor PlutusV1
            PlutusV2Event{} -> case ctxV2 of
                Just (ctx, params) -> InvalidResult <$> checkEvaluationEvent ctx params event
                Nothing            -> Just $ MissingCostParametersFor PlutusV2

main :: IO ()
main = do
    dir <- getEnv "EVENT_DUMP_DIR"
    eventFiles <- filter ("event" `isExtensionOf`) <$> listFiles dir
    defaultMain . testGroup "Mainnet script evaluation test" $ fmap testOneFile eventFiles
