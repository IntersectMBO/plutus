{-# LANGUAGE DeriveAnyClass   #-}
{-# LANGUAGE TypeApplications #-}

module LoadScriptEvents (eventsOf, loadEvents)
where

import PlutusLedgerApi.Common
import PlutusLedgerApi.Test.EvaluationEvent

import Codec.Serialise (Serialise, readFileDeserialise)
import Data.Int (Int64)
import Data.List.NonEmpty (NonEmpty, toList)
import GHC.Generics (Generic)


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
    , dataInputs2          :: [Data]
    }
    deriving stock (Show, Generic)
    deriving anyclass (Serialise)

data ScriptEvaluationEvent2
    = PlutusV1Event2 ScriptEvaluationData2 ScriptEvaluationResult
    | PlutusV2Event2 ScriptEvaluationData2 ScriptEvaluationResult
    deriving stock (Show, Generic)
    deriving anyclass (Serialise)

data ScriptEvaluationEvents2 = ScriptEvaluationEvents2
    { eventsCostParamsV1' :: Maybe [Int64]
    -- ^ Cost parameters shared by all PlutusV1 evaluation events in `eventsEvents`, if any.
    , eventsCostParamsV2' :: Maybe [Int64]
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

-- Loading events from a file
loadEvents :: FilePath -> IO ScriptEvaluationEvents
loadEvents eventFile =
  events2toEvents <$> readFileDeserialise @ScriptEvaluationEvents2 eventFile

eventsOf :: ScriptEvaluationEvents -> [ScriptEvaluationEvent]
eventsOf = toList . eventsEvents
