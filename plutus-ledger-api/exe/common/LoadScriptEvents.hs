{-# LANGUAGE TypeApplications #-}

module LoadScriptEvents (eventsOf, loadEvents) where

import Codec.Serialise (readFileDeserialise)
import Data.List.NonEmpty (toList)
import PlutusLedgerApi.Test.EvaluationEvent

-- Loading events from a file
loadEvents :: FilePath -> IO ScriptEvaluationEvents
loadEvents = readFileDeserialise @ScriptEvaluationEvents

eventsOf :: ScriptEvaluationEvents -> [ScriptEvaluationEvent]
eventsOf = toList . eventsEvents
