{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}

module PlutusLedgerApi.Test.EvaluationEvent
  ( ScriptEvaluationEvents (..)
  , ScriptEvaluationEvent (..)
  , ScriptEvaluationData (..)
  , ScriptEvaluationResult (..)
  , UnexpectedEvaluationResult (..)
  , TestFailure (..)
  , renderTestFailure
  , renderTestFailures
  , checkEvaluationEvent
  ) where

import PlutusCore.Data qualified as PLC
import PlutusCore.Pretty
import PlutusLedgerApi.Common
import PlutusLedgerApi.V1 qualified as V1
import PlutusLedgerApi.V2 qualified as V2

import Codec.Serialise (Serialise (..))
import Data.ByteString.Base64 qualified as Base64
import Data.ByteString.Short qualified as BS
import Data.Int (Int64)
import Data.List.NonEmpty (NonEmpty, toList)
import Data.Text.Encoding qualified as Text
import GHC.Generics (Generic)
import PlutusLedgerApi.V3 qualified as V3
import Prettyprinter

data ScriptEvaluationResult = ScriptEvaluationSuccess | ScriptEvaluationFailure
  deriving stock (Show, Generic)
  deriving anyclass (Serialise)

instance Pretty ScriptEvaluationResult where
  pretty = viaShow

{-| All the data needed to evaluate a script using the ledger API, except for the cost model
 parameters, as these are tracked separately. -}
data ScriptEvaluationData = ScriptEvaluationData
  { dataProtocolVersion :: MajorProtocolVersion
  , dataBudget :: ExBudget
  , dataScript :: SerialisedScript
  , dataInputs :: [PLC.Data]
  }
  deriving stock (Show, Generic)
  deriving anyclass (Serialise)

instance Pretty ScriptEvaluationData where
  pretty ScriptEvaluationData {..} =
    vsep
      [ "major protocol version:" <+> pretty dataProtocolVersion
      , "budget: " <+> pretty dataBudget
      , "script: " <+> pretty (Text.decodeLatin1 . Base64.encode $ BS.fromShort dataScript)
      , "data: " <+> nest 2 (vsep $ pretty <$> dataInputs)
      ]

{-| Information about an on-chain script evaluation event, specifically the information needed
 to evaluate the script, and the expected result. -}
data ScriptEvaluationEvent
  = PlutusEvent PlutusLedgerLanguage ScriptEvaluationData ScriptEvaluationResult
  deriving stock (Show, Generic)
  deriving anyclass (Serialise)

instance Pretty ScriptEvaluationEvent where
  pretty (PlutusEvent plutusLedgerVersion d res) =
    nest 2 $
      vsep
        [ "PlutusEvent"
        , pretty plutusLedgerVersion
        , pretty d
        , pretty res
        ]

{-| This type contains a list of on-chain script evaluation events. All PlutusV1
 evaluations (if any) share the same cost parameters. Same with PlutusV2.

 Sharing the cost parameters lets us avoid creating a new `EvaluationContext` for
 each `ScriptEvaluationEvent`. -}
data ScriptEvaluationEvents = ScriptEvaluationEvents
  { eventsCostParamsV1 :: Maybe [Int64]
  -- ^ Cost parameters shared by all PlutusV1 evaluation events in `eventsEvents`, if any.
  , eventsCostParamsV2 :: Maybe [Int64]
  -- ^ Cost parameters shared by all PlutusV2 evaluation events in `eventsEvents`, if any.
  , eventsEvents :: NonEmpty ScriptEvaluationEvent
  }
  deriving stock (Generic)
  deriving anyclass (Serialise)

-- | Error type when re-evaluating a `ScriptEvaluationEvent`.
data UnexpectedEvaluationResult
  = UnexpectedEvaluationSuccess
      ScriptEvaluationEvent
      [Int64]
      -- ^ Cost parameters
      ExBudget
      -- ^ Actual budget consumed
  | UnexpectedEvaluationFailure
      ScriptEvaluationEvent
      [Int64]
      -- ^ Cost parameters
      EvaluationError
  | DecodeError ScriptDecodeError
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
    DecodeError err ->
      nest 2 $
        vsep
          [ "ScriptDecodeError"
          , pretty err
          , "This should never happen at phase 2!"
          ]

data TestFailure
  = InvalidResult UnexpectedEvaluationResult
  | MissingCostParametersFor PlutusLedgerLanguage

renderTestFailure :: TestFailure -> String
renderTestFailure = \case
  InvalidResult err -> display err
  MissingCostParametersFor lang ->
    "Missing cost parameters for "
      ++ show lang
      ++ ".\n"
      ++ "Report this as a bug against the script dumper in plutus-apps."

renderTestFailures :: NonEmpty TestFailure -> String
renderTestFailures testFailures =
  "Number of failed test cases: "
    ++ show (length testFailures)
    ++ ".\n"
    ++ unwords (map renderTestFailure (toList testFailures))

-- | Re-evaluate an on-chain script evaluation event.
checkEvaluationEvent
  :: EvaluationContext
  -> [Int64]
  -- ^ Cost parameters
  -> ScriptEvaluationEvent
  -> Maybe UnexpectedEvaluationResult
checkEvaluationEvent ctx params ev = case ev of
  PlutusEvent PlutusV1 ScriptEvaluationData {..} expected ->
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
      Left err -> Just (DecodeError err)
  PlutusEvent PlutusV2 ScriptEvaluationData {..} expected ->
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
      Left err -> Just (DecodeError err)
  PlutusEvent PlutusV3 ScriptEvaluationData {..} expected ->
    case deserialiseScript PlutusV3 dataProtocolVersion dataScript of
      Right script -> do
        dataInput <-
          case dataInputs of
            [input] -> Just input
            _ -> Nothing
        let (_, actual) =
              V3.evaluateScriptRestricting
                dataProtocolVersion
                V3.Quiet
                ctx
                dataBudget
                script
                dataInput
        verify expected actual
      Left err -> Just (DecodeError err)
  where
    verify ScriptEvaluationSuccess (Left err) =
      Just $ UnexpectedEvaluationFailure ev params err
    verify ScriptEvaluationFailure (Right budget) =
      Just $ UnexpectedEvaluationSuccess ev params budget
    verify _ _ =
      Nothing
