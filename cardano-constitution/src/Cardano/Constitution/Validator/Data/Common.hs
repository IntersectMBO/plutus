-- editorconfig-checker-disable-file
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE Strict            #-}
{-# LANGUAGE TypeApplications  #-}
{-# LANGUAGE ViewPatterns      #-}
module Cardano.Constitution.Validator.Data.Common
    ( withChangedParams
    , ChangedParams
    , ConstitutionValidator
    , validateParamValue
    ) where

import Control.Category hiding ((.))

import Cardano.Constitution.Config
import Data.Coerce
import PlutusLedgerApi.Data.V3
import PlutusTx.Builtins qualified as B
import PlutusTx.Builtins.Internal qualified as BI
import PlutusTx.Data.AssocMap
import PlutusTx.NonCanonicalRational as NCRatio
import PlutusTx.Prelude as Tx hiding (toList)

type ConstitutionValidator = ScriptContext -- ^ ScriptContext, deep inside is the changed-parameters proposal
                           -> BuiltinUnit -- ^ No-error means the proposal conforms to the constitution

-- OPTIMIZE: operate on BuiltinList<BuiltinPair> directly, needs major refactoring of sorted&unsorted Validators
type ChangedParams = [(BuiltinData, BuiltinData)]

{- HLINT ignore "Redundant lambda" -} -- I like to see until where it supposed to be first applied.
{- HLINT ignore "Collapse lambdas" -} -- I like to see and comment on each arg
withChangedParams :: (ChangedParams -> Bool) -> ConstitutionValidator
withChangedParams fun (scriptContextToValidGovAction -> validGovAction) =
    case validGovAction of
        Just cparams ->  if fun cparams
            then BI.unitval
            else traceError "ChangedParams failed to validate"
        Nothing -> BI.unitval -- this is a treasury withdrawal, we just accept it
{-# INLINABLE withChangedParams #-}

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
          Tx.all validatePredAppliedToActual preds

      validatePred :: forall a. Tx.Ord a => a -> Predicate a -> Bool
      validatePred actualValue (predKey, expectedPredValues) =
          Tx.all meaningWithActual expectedPredValues
        where
          -- we find the meaning (function) from the PredKey
          meaning = defaultPredMeanings predKey
          -- apply the meaning to actual value: expectedValue is 1st argument, actualValue is 2nd argument
          meaningWithActual = (`meaning` actualValue)
{-# INLINABLE validateParamValue #-}

scriptContextToValidGovAction :: ScriptContext -> Maybe ChangedParams
scriptContextToValidGovAction ScriptContext {scriptContextScriptInfo = scriptInfo} =
    case scriptInfo of
        ProposingScript _ ProposalProcedure { ppGovernanceAction = ppGovAct } ->
            case ppGovAct of
                ParameterChange _ cparams _ -> Just (B.unsafeDataAsMap . toBuiltinData $ cparams)
                TreasuryWithdrawals _ _ -> Nothing
                _ -> traceError "Not a ChangedParams or TreasuryWithdrawals. This should not ever happen, because ledger should guard before, against it."
        _ -> Nothing
{-# INLINABLE scriptContextToValidGovAction #-}
