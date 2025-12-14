-- editorconfig-checker-disable-file
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE Strict #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE NoImplicitPrelude #-}

module Cardano.Constitution.Validator.Common
  ( withChangedParams
  , ChangedParams
  , ConstitutionValidator
  , validateParamValue
  ) where

import Control.Category hiding ((.))

import Cardano.Constitution.Config
import Data.Coerce
import PlutusLedgerApi.V3 as V3
import PlutusTx.Builtins qualified as B
import PlutusTx.Builtins.Internal qualified as BI
import PlutusTx.List as List
import PlutusTx.NonCanonicalRational as NCRatio
import PlutusTx.Prelude as Tx

type ConstitutionValidator =
  BuiltinData
  -- ^ ScriptContext, deep inside is the changed-parameters proposal
  -> BuiltinUnit
  -- ^ No-error means the proposal conforms to the constitution

-- OPTIMIZE: operate on BuiltinList<BuiltinPair> directly, needs major refactoring of sorted&unsorted Validators
type ChangedParams = [(BuiltinData, BuiltinData)]

{- HLINT ignore "Redundant lambda" -}
-- I like to see until where it supposed to be first applied.
{- HLINT ignore "Collapse lambdas" -}
-- I like to see and comment on each arg
withChangedParams :: (ChangedParams -> Bool) -> ConstitutionValidator
withChangedParams fun (scriptContextToValidGovAction -> validGovAction) =
  case validGovAction of
    Just cparams ->
      if fun cparams
        then BI.unitval
        else traceError "ChangedParams failed to validate"
    Nothing -> BI.unitval -- this is a treasury withdrawal, we just accept it
{-# INLINEABLE withChangedParams #-}

validateParamValue :: ParamValue -> BuiltinData -> Bool
validateParamValue = \case
  ParamInteger preds -> validatePreds preds . B.unsafeDataAsI
  ParamRational preds -> validatePreds preds . coerce . unsafeFromBuiltinData @NonCanonicalRational
  ParamList paramValues -> validateParamValues paramValues . BI.unsafeDataAsList
  -- accept the actual proposed value without examining it
  ParamAny -> const True
  where
    validateParamValues :: [ParamValue] -> BI.BuiltinList BuiltinData -> Bool
    validateParamValues = \case
      (paramValueHd : paramValueTl) -> \actualValueData ->
        -- if actualValueData is not a cons, it will error
        validateParamValue paramValueHd (BI.head actualValueData)
          && validateParamValues paramValueTl (BI.tail actualValueData)
      -- if reached the end of list of param-values to check, ensure no more proposed data are left
      [] -> B.fromOpaque . BI.null

    validatePreds :: forall a. Tx.Ord a => Predicates a -> a -> Bool
    validatePreds (Predicates preds) (validatePred -> validatePredAppliedToActual) =
      List.all validatePredAppliedToActual preds

    validatePred :: forall a. Tx.Ord a => a -> Predicate a -> Bool
    validatePred actualValue (predKey, expectedPredValues) =
      List.all meaningWithActual expectedPredValues
      where
        -- we find the meaning (function) from the PredKey
        meaning = defaultPredMeanings predKey
        -- apply the meaning to actual value: expectedValue is 1st argument, actualValue is 2nd argument
        meaningWithActual = (`meaning` actualValue)
{-# INLINEABLE validateParamValue #-}

scriptContextToValidGovAction :: BuiltinData -> Maybe ChangedParams
scriptContextToValidGovAction =
  scriptContextToScriptInfo
    >>> scriptInfoToProposalProcedure
    >>> proposalProcedureToGovernanceAction
    >>> governanceActionToValidGovAction
  where
    scriptContextToScriptInfo :: BuiltinData -> BuiltinData -- aka ScriptContext -> ScriptInfo
    scriptContextToScriptInfo =
      BI.unsafeDataAsConstr
        >>> BI.snd
        >>> BI.tail
        >>> BI.tail
        >>> BI.head

    scriptInfoToProposalProcedure :: BuiltinData -> BuiltinData
    scriptInfoToProposalProcedure (BI.unsafeDataAsConstr -> si) =
      if BI.fst si `B.equalsInteger` 5 -- Constructor Index of `ProposingScript`
        then BI.head (BI.tail (BI.snd si))
        else traceError "Not a ProposalProcedure. This should not ever happen, because ledger should guard before, against it."

    proposalProcedureToGovernanceAction :: BuiltinData -> BuiltinData
    proposalProcedureToGovernanceAction =
      BI.unsafeDataAsConstr
        >>> BI.snd
        >>> BI.tail
        >>> BI.tail
        >>> BI.head

    governanceActionToValidGovAction :: BuiltinData -> Maybe ChangedParams
    governanceActionToValidGovAction (BI.unsafeDataAsConstr -> govAction@(BI.fst -> govActionConstr))
      -- Constructor Index of `ChangedParams` is 0
      | govActionConstr `B.equalsInteger` 0 = Just (B.unsafeDataAsMap (BI.head (BI.tail (BI.snd govAction))))
      -- Constructor Index of `TreasuryWithdrawals` is 2
      | govActionConstr `B.equalsInteger` 2 = Nothing -- means treasurywithdrawal
      | otherwise = traceError "Not a ChangedParams or TreasuryWithdrawals. This should not ever happen, because ledger should guard before, against it."
{-# INLINEABLE scriptContextToValidGovAction #-}
