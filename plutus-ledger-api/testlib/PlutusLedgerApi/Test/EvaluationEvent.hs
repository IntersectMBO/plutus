{-# LANGUAGE DeriveAnyClass #-}

module PlutusLedgerApi.Test.EvaluationEvent (
    ScriptEvaluationEvents (..),
    ScriptEvaluationEvent (..),
    ScriptEvaluationData (..),
    ScriptEvaluationResult (..),
) where

import PlutusCore.Data qualified as PLC
import PlutusCore.Evaluation.Machine.ExBudget (ExBudget)
import PlutusLedgerApi.Common

import Codec.Serialise (Serialise (..))
import Data.List.NonEmpty (NonEmpty)
import GHC.Generics (Generic)

data ScriptEvaluationResult = ScriptEvaluationSuccess | ScriptEvaluationFailure
    deriving stock (Generic)
    deriving anyclass (Serialise)

data ScriptEvaluationData = ScriptEvaluationData
    { dataProtocolVersion :: ProtocolVersion
    , dataBudget          :: ExBudget
    , dataScript          :: SerialisedScript
    , dataInputs          :: [PLC.Data]
    }
    deriving stock (Generic)
    deriving anyclass (Serialise)

data ScriptEvaluationEvent
    = PlutusV1Event ScriptEvaluationData ScriptEvaluationResult
    | PlutusV2Event ScriptEvaluationData ScriptEvaluationResult
    deriving stock (Generic)
    deriving anyclass (Serialise)

data ScriptEvaluationEvents = ScriptEvaluationEvents
    { eventsCostParamsV1 :: Maybe [Integer]
    -- ^ Cost parameters shared by all PlutusV1 evaluation events in `eventsEvents`, if any.
    , eventsCostParamsV2 :: Maybe [Integer]
    -- ^ Cost parameters shared by all PlutusV2 evaluation events in `eventsEvents`, if any.
    , eventsEvents       :: NonEmpty ScriptEvaluationEvent
    }
    deriving stock (Generic)
    deriving anyclass (Serialise)
