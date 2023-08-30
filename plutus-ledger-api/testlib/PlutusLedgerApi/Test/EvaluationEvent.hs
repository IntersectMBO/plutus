{-# LANGUAGE DeriveAnyClass    #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes       #-}
{-# LANGUAGE RecordWildCards   #-}

module PlutusLedgerApi.Test.EvaluationEvent (
    ScriptEvaluationEvents (..),
    ScriptEvaluationEvent (..),
    ScriptEvaluationData (..),
    ScriptEvaluationResult (..),
    UnexpectedEvaluationResult (..),
    TestFailure (..),
    renderTestFailure,
    renderTestFailures,
    checkEvaluationEvent,
) where

import PlutusCore.Data qualified as PLC
import PlutusCore.Pretty
import PlutusLedgerApi.Common
import PlutusLedgerApi.V1 qualified as V1
import PlutusLedgerApi.V2 qualified as V2

import Codec.Serialise (Serialise (..))
import Data.ByteString.Base64 qualified as Base64
import Data.ByteString.Short qualified as BS
import Data.List.NonEmpty (NonEmpty, toList)
import Data.Text.Encoding qualified as Text
import GHC.Generics (Generic)
import Prettyprinter
import PyF (fmt)


data ScriptEvaluationResult = ScriptEvaluationSuccess | ScriptEvaluationFailure
    deriving stock (Show, Generic)
    deriving anyclass (Serialise)

instance Pretty ScriptEvaluationResult where
    pretty = viaShow

{- | All the data needed to evaluate a script using the ledger API, except for the cost model
 parameters, as these are tracked separately.
-}
data ScriptEvaluationData = ScriptEvaluationData
    { dataProtocolVersion :: ProtocolVersion
    , dataBudget          :: ExBudget
    , dataScript          :: SerialisedScript
    , dataInputs          :: [PLC.Data]
    }
    deriving stock (Show, Generic)
    deriving anyclass (Serialise)

instance Pretty ScriptEvaluationData where
    pretty ScriptEvaluationData{..} =
        vsep
            [ "protocol version:" <+> pretty dataProtocolVersion
            , "budget: " <+> pretty dataBudget
            , "script: " <+> pretty (Text.decodeLatin1 . Base64.encode $ BS.fromShort dataScript)
            , "data: " <+> nest 2 (vsep $ pretty <$> dataInputs)
            ]

{- | Information about an on-chain script evaluation event, specifically the information needed
 to evaluate the script, and the expected result.
-}
data ScriptEvaluationEvent
    = PlutusV1Event ScriptEvaluationData ScriptEvaluationResult
    | PlutusV2Event ScriptEvaluationData ScriptEvaluationResult
    deriving stock (Show, Generic)
    deriving anyclass (Serialise)

instance Pretty ScriptEvaluationEvent where
    pretty = \case
        PlutusV1Event d res ->
            nest 2 $
                vsep
                    [ "PlutusV1Event"
                    , pretty d
                    , pretty res
                    ]
        PlutusV2Event d res ->
            nest 2 $
                vsep
                    [ "PlutusV2Event"
                    , pretty d
                    , pretty res
                    ]

{- | This type contains a list of on-chain script evaluation events. All PlutusV1
 evaluations (if any) share the same cost parameters. Same with PlutusV2.

 Sharing the cost parameters lets us avoid creating a new `EvaluationContext` for
 each `ScriptEvaluationEvent`.
-}
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
    = UnexpectedEvaluationSuccess
        ScriptEvaluationEvent
        [Integer]
        -- ^ Cost parameters
        ExBudget
        -- ^ Actual budget consumed
    | UnexpectedEvaluationFailure
        ScriptEvaluationEvent
        [Integer]
        -- ^ Cost parameters
        EvaluationError
    deriving stock (Show)

instance Pretty UnexpectedEvaluationResult where
    pretty = \case
        UnexpectedEvaluationSuccess ev params budget ->
            nest 2 $
                vsep
                    [ "UnexpectedEvaluationSuccess"
                    , pretty ev
                    , "Cost parameters:" <+> pretty params
                    , "Budget spent:" <+> pretty budget
                    ]
        UnexpectedEvaluationFailure ev params err ->
            nest 2 $
                vsep
                    [ "UnexpectedEvaluationFailure"
                    , pretty ev
                    , "Cost parameters:" <+> pretty params
                    , "Evaluation error:" <+> pretty err
                    ]

data TestFailure
    = InvalidResult UnexpectedEvaluationResult
    | MissingCostParametersFor PlutusLedgerLanguage

renderTestFailure :: TestFailure -> String
renderTestFailure = \case
    InvalidResult err -> display err
    MissingCostParametersFor lang -> [fmt|
        Missing cost parameters for {show lang}.
        Report this as a bug against the script dumper in plutus-apps.
    |]

renderTestFailures :: NonEmpty TestFailure -> String
renderTestFailures xs = [fmt|
    Number of failed test cases: {length xs}
    {unlines . fmap renderTestFailure $ toList xs}
|]

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
        Just $ UnexpectedEvaluationFailure ev params err
    verify ScriptEvaluationFailure (Right budget) =
        Just $ UnexpectedEvaluationSuccess ev params budget
    verify _ _ = Nothing
