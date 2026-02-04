{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE Strict #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}
{-# OPTIONS_GHC -fno-full-laziness #-}
{-# OPTIONS_GHC -fno-ignore-interface-pragmas #-}
{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}
{-# OPTIONS_GHC -fno-spec-constr #-}
{-# OPTIONS_GHC -fno-specialise #-}
{-# OPTIONS_GHC -fno-strictness #-}
{-# OPTIONS_GHC -fno-unbox-small-strict-fields #-}
{-# OPTIONS_GHC -fno-unbox-strict-fields #-}
{-# OPTIONS_GHC -fplugin PlutusTx.Plugin #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:conservative-optimisation #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:datatypes=BuiltinCasing #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:no-remove-trace #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:preserve-logging #-}

module LinearVesting.Validator where

import PlutusTx
import PlutusTx.Builtins.Internal qualified as BI
import PlutusTx.Prelude
import Prelude qualified as Haskell

import PlutusLedgerApi.Data.V3
import PlutusLedgerApi.V1.Data.Value (AssetClass, assetClassValueOf)
import PlutusLedgerApi.V3.Data.Contexts (txSignedBy)
import PlutusTx.Data.List (List)
import PlutusTx.Data.List qualified as List

{-# ANN module ("onchain-contract" :: Haskell.String) #-}

data VestingDatum = VestingDatum
  { beneficiary :: Address
  , vestingAsset :: AssetClass
  , totalVestingQty :: Integer
  , vestingPeriodStart :: Integer
  , vestingPeriodEnd :: Integer
  , firstUnlockPossibleAfter :: Integer
  , totalInstallments :: Integer
  }
  deriving stock (Haskell.Show)

$(makeLift ''VestingDatum)
$(makeIsDataIndexed ''VestingDatum [('VestingDatum, 0)])

data VestingRedeemer = PartialUnlock | FullUnlock

$(PlutusTx.makeLift ''VestingRedeemer)
$( PlutusTx.makeIsDataIndexed
     ''VestingRedeemer
     [('PartialUnlock, 0), ('FullUnlock, 1)]
 )

countInputsAtScript :: ScriptHash -> List TxInInfo -> Integer
countInputsAtScript scriptHash = go 0
  where
    go :: Integer -> List TxInInfo -> Integer
    go n = List.caseList' n \txIn txIns ->
      case addressCredential (txOutAddress (txInInfoResolved txIn)) of
        ScriptCredential vh | vh == scriptHash -> go (n + 1) txIns
        _ -> go n txIns

validateVestingPartialUnlock :: ScriptContext -> Bool
validateVestingPartialUnlock ctx =
  let
    txInfo :: TxInfo = scriptContextTxInfo ctx
    SpendingScript ownRef (Just (Datum datum)) = scriptContextScriptInfo ctx
    vestingDatum :: VestingDatum = unsafeFromBuiltinData datum
    inputs = txInfoInputs txInfo

    Just ownVestingInput = List.find ((== ownRef) . txInInfoOutRef) inputs
    resolvedOut = txInInfoResolved ownVestingInput
    inputAddress = txOutAddress resolvedOut

    ScriptCredential scriptHash = addressCredential inputAddress
    Just ownVestingOutput =
      List.find ((== inputAddress) . txOutAddress) (txInfoOutputs txInfo)
    outputDatum = txOutDatum ownVestingOutput

    divCeil :: Integer -> Integer -> Integer
    divCeil x y = 1 + (x - 1) `divide` y

    asset :: AssetClass =
      vestingAsset vestingDatum
    oldRemainingQty :: Integer =
      assetClassValueOf (txOutValue resolvedOut) asset
    newRemainingQty :: Integer =
      assetClassValueOf (txOutValue ownVestingOutput) asset
    vestingPeriodLength :: Integer =
      vestingPeriodEnd vestingDatum - vestingPeriodStart vestingDatum
    currentTimeApproximation :: Integer =
      getPOSIXTime (getLowerInclusiveTimeRange (txInfoValidRange txInfo))
    vestingTimeRemaining :: Integer =
      vestingPeriodEnd vestingDatum - currentTimeApproximation
    timeBetweenTwoInstallments :: Integer =
      vestingPeriodLength `divCeil` totalInstallments vestingDatum
    futureInstallments :: Integer =
      vestingTimeRemaining `divCeil` timeBetweenTwoInstallments
    expectedRemainingQty :: Integer =
      (futureInstallments * totalVestingQty vestingDatum)
        `divCeil` totalInstallments vestingDatum
    PubKeyCredential beneficiaryHash =
      addressCredential (beneficiary vestingDatum)
   in
    if
      | not (txSignedBy txInfo beneficiaryHash) ->
          traceError "Missing beneficiary signature"
      | firstUnlockPossibleAfter vestingDatum >= currentTimeApproximation ->
          traceError "Unlock not permitted until firstUnlockPossibleAfter time"
      | newRemainingQty <= 0 ->
          traceError "Zero remaining assets not allowed"
      | newRemainingQty >= oldRemainingQty ->
          traceError "Remaining asset is not decreasing"
      | expectedRemainingQty /= newRemainingQty ->
          traceError "Mismatched remaining asset"
      | txOutDatum resolvedOut /= outputDatum ->
          traceError "Datum Modification Prohibited"
      | countInputsAtScript scriptHash inputs /= 1 ->
          traceError "Double satisfaction"
      | otherwise ->
          True

validateVestingFullUnlock :: ScriptContext -> Bool
validateVestingFullUnlock ctx =
  let
    txInfo :: TxInfo = scriptContextTxInfo ctx
    currentTimeApproximation :: Integer =
      getPOSIXTime (getLowerInclusiveTimeRange (txInfoValidRange txInfo))
    SpendingScript _ownRef (Just (Datum datum)) = scriptContextScriptInfo ctx
    vestingDatum :: VestingDatum = unsafeFromBuiltinData datum
    PubKeyCredential beneficiaryKey = addressCredential (beneficiary vestingDatum)
   in
    BI.ifThenElse
      (not (txSignedBy txInfo beneficiaryKey))
      (\_ -> traceError "Missing beneficiary signature")
      ( \_ ->
          BI.ifThenElse
            (vestingPeriodEnd vestingDatum >= currentTimeApproximation)
            (\_ -> traceError "Unlock not permitted until vestingPeriodEnd time")
            (\_ -> True)
            BI.unitval
      )
      BI.unitval

getLowerInclusiveTimeRange :: POSIXTimeRange -> POSIXTime
getLowerInclusiveTimeRange = \case
  Interval (LowerBound (Finite posixTime) inclusive) _upperBound ->
    if inclusive then posixTime else posixTime + 1
  _ -> traceError "Time range not Finite"

-- Evaluation was SUCCESSFUL, result is:
--   ()

-- Execution budget spent:
--   CPU 30,837,131
--   MEM 131,619

-- Evaluation traces:
--   1. Parsing ScriptContext...
--   2. Parsed ScriptContext
--   3. Parsed Redeemer
--   4. Full unlock requested
--   5. Validation completed
{-# INLINEABLE typedValidator #-}
typedValidator :: ScriptContext -> Bool
typedValidator context =
  trace "Validation completed"
    $ case redeemer of
      FullUnlock ->
        validateVestingFullUnlock $ trace "Full unlock requested" context
      PartialUnlock ->
        validateVestingPartialUnlock $ trace "Partial unlock requested" context
  where
    {-# INLINEABLE redeemer #-}
    redeemer :: VestingRedeemer
    redeemer =
      case fromBuiltinData (getRedeemer (scriptContextRedeemer context)) of
        Nothing -> traceError "Failed to parse Redeemer"
        Just r -> trace "Parsed Redeemer" r

{-# INLINEABLE untypedValidator #-}
untypedValidator :: BuiltinData -> BuiltinUnit
untypedValidator scriptContextData =
  case trace "Parsing ScriptContext..." (fromBuiltinData scriptContextData) of
    Nothing -> traceError "Failed to parse ScriptContext"
    Just ctx -> check $ typedValidator $ trace "Parsed ScriptContext" ctx

validatorCode :: CompiledCode (BuiltinData -> BuiltinUnit)
validatorCode = $$(compile [||untypedValidator||])
