{-# LANGUAGE DeriveAnyClass  #-}
{-# LANGUAGE RecordWildCards #-}

module PlutusLedgerApi.Test.EvaluationEvent (
    ScriptEvaluationEvents (..),
    ScriptEvaluationEvent (..),
    ScriptEvaluationData (..),
    ScriptEvaluationResult (..),
    UnexpectedEvaluationResult (..),
    checkEvaluationEvent,
) where

import PlutusCore.Data qualified as PLC
import PlutusCore.Evaluation.Machine.ExBudget (ExBudget)
import PlutusLedgerApi.Common

import Codec.Serialise (Serialise (..))
import Data.List.NonEmpty (NonEmpty)
import GHC.Generics (Generic)
import PlutusLedgerApi.V1 qualified as V1
import PlutusLedgerApi.V2 qualified as V2

data ScriptEvaluationResult = ScriptEvaluationSuccess | ScriptEvaluationFailure
    deriving stock (Generic)
    deriving anyclass (Serialise)

-- | Data used for an on-chain script evaluation.
data ScriptEvaluationData = ScriptEvaluationData
    { dataProtocolVersion :: ProtocolVersion
    , dataBudget          :: ExBudget
    , dataScript          :: SerialisedScript
    , dataInputs          :: [PLC.Data]
    }
    deriving stock (Generic)
    deriving anyclass (Serialise)

-- | Information about an on-chain script evaluation event, specifically the information needed to evaluate the script, and the expected result.
data ScriptEvaluationEvent
    = PlutusV1Event ScriptEvaluationData ScriptEvaluationResult
    | PlutusV2Event ScriptEvaluationData ScriptEvaluationResult
    deriving stock (Generic)
    deriving anyclass (Serialise)

-- | This type contains a list of on-chain script evaluation events. All PlutusV1
-- evaluations (if any) share the same cost parameters. Same with PlutusV2.
--
-- Sharing the cost parameters lets us avoid creating a new `EvaluationContext` for
-- each `ScriptEvaluationEvent`.
data ScriptEvaluationEvents = ScriptEvaluationEvents
    { eventsCostParamsV1 :: Maybe [Integer]
    -- ^ Cost parameters shared by all PlutusV1 evaluation events in `eventsEvents`, if any.
    , eventsCostParamsV2 :: Maybe [Integer]
    -- ^ Cost parameters shared by all PlutusV2 evaluation events in `eventsEvents`, if any.
    , eventsEvents       :: NonEmpty ScriptEvaluationEvent
    }
    deriving stock (Generic)
    deriving anyclass (Serialise)

-- | Error type when re-evaluating a `ScriptEvaluationEvent`.
data UnexpectedEvaluationResult
    = UnexpectedEvaluationResult
        ScriptEvaluationEvent
        [Integer]
        -- ^ Cost parameters
        (Either EvaluationError ExBudget)
        -- ^ Actual evaluation outcome

-- | Re-evaluate an on-chain script evaluation event.
checkEvaluationEvent ::
    EvaluationContext ->
    -- | Cost parameters
    [Integer] ->
    ScriptEvaluationEvent ->
    Maybe UnexpectedEvaluationResult
checkEvaluationEvent ctx params ev = case ev of
    PlutusV1Event ScriptEvaluationData{..} expected ->
        let (_, actual) =
                V1.evaluateScriptRestricting
                    dataProtocolVersion
                    V1.Quiet
                    ctx
                    dataBudget
                    dataScript
                    dataInputs
         in verify expected actual
    PlutusV2Event ScriptEvaluationData{..} expected ->
        let (_, actual) =
                V2.evaluateScriptRestricting
                    dataProtocolVersion
                    V2.Quiet
                    ctx
                    dataBudget
                    dataScript
                    dataInputs
         in verify expected actual
  where
    verify ScriptEvaluationSuccess (Left err) =
        Just $ UnexpectedEvaluationResult ev params (Left err)
    verify ScriptEvaluationFailure (Right budget) =
        Just $ UnexpectedEvaluationResult ev params (Right budget)
    verify _ _ = Nothing
