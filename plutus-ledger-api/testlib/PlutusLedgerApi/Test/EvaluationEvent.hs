{-# LANGUAGE DeriveAnyClass #-}

module PlutusLedgerApi.Test.EvaluationEvent (
    ScriptEvaluationEvent (..),
    ScriptEvaluationEventPlutusV1 (..),
    ScriptEvaluationEventPlutusV2 (..),
    ScriptEvaluationData (..),
    ScriptEvaluationResult (..),
) where

import PlutusCore.Data qualified as PLC
import PlutusCore.Evaluation.Machine.ExBudget (ExBudget)
import PlutusLedgerApi.Common

import Codec.Serialise (Serialise (..))
import GHC.Generics (Generic)

data ScriptEvaluationResult = ScriptEvaluationSuccess | ScriptEvaluationFailure
    deriving stock (Generic)
    deriving anyclass (Serialise)

data ScriptEvaluationData = ScriptEvaluationData
    { dataProtocolVersion :: ProtocolVersion
    , dataCostParams      :: [Integer]
    , dataBudget          :: ExBudget
    , dataScript          :: SerialisedScript
    , dataInputs          :: [PLC.Data]
    }
    deriving stock (Generic)
    deriving anyclass (Serialise)

data ScriptEvaluationEventPlutusV1 = ScriptEvaluationEventPlutusV1
    { v1Data   :: ScriptEvaluationData
    , v1Result :: ScriptEvaluationResult
    }
    deriving stock (Generic)
    deriving anyclass (Serialise)

data ScriptEvaluationEventPlutusV2 = ScriptEvaluationEventPlutusV2
    { v2Data   :: ScriptEvaluationData
    , v2Result :: ScriptEvaluationResult
    }
    deriving stock (Generic)
    deriving anyclass (Serialise)

data ScriptEvaluationEvent
    = PlutusV1Event ScriptEvaluationEventPlutusV1
    | PlutusV2Event ScriptEvaluationEventPlutusV2
    deriving stock (Generic)
    deriving anyclass (Serialise)
