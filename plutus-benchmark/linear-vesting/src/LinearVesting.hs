{-# LANGUAGE BangPatterns          #-}
{-# LANGUAGE BlockArguments        #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE MultiWayIf            #-}
{-# LANGUAGE NamedFieldPuns        #-}
{-# LANGUAGE NoImplicitPrelude     #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE PatternSynonyms       #-}
{-# LANGUAGE Strict                #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE ViewPatterns          #-}
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
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:no-remove-trace #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:preserve-logging #-}

module LinearVesting where

import PlutusTx
import PlutusTx.Prelude
import Prelude qualified as Haskell

import PlutusLedgerApi.Data.V3
import PlutusLedgerApi.V1.Data.Value (AssetClass, assetClass, assetClassValueOf)
import PlutusLedgerApi.V3.Data.Contexts (txSignedBy)
import PlutusTx.Data.AssocMap qualified as Map
import PlutusTx.Data.List (List)
import PlutusTx.Data.List qualified as List

data VestingDatum = VestingDatum
  { beneficiary              :: Address
  , vestingAsset             :: AssetClass
  , totalVestingQty          :: Integer
  , vestingPeriodStart       :: Integer
  , vestingPeriodEnd         :: Integer
  , firstUnlockPossibleAfter :: Integer
  , totalInstallments        :: Integer
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
      _                                      -> go n txIns

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
    if
      | not (txSignedBy txInfo beneficiaryKey) ->
          traceError "Missing beneficiary signature"
      | vestingPeriodEnd vestingDatum >= currentTimeApproximation ->
          traceError "Unlock not permitted until vestingPeriodEnd time"
      | otherwise ->
          True

getLowerInclusiveTimeRange :: POSIXTimeRange -> POSIXTime
getLowerInclusiveTimeRange = \case
  Interval (LowerBound (Finite posixTime) inclusive) _upperBound ->
    if inclusive then posixTime else posixTime + 1
  _ -> traceError "Time range not Finite"

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
      Just r  -> trace "Parsed Redeemer" r

{-# INLINEABLE untypedValidator #-}
untypedValidator :: BuiltinData -> BuiltinUnit
untypedValidator scriptContextData =
  case trace "Parsing ScriptContext..." (fromBuiltinData scriptContextData) of
    Nothing  -> traceError "Failed to parse ScriptContext"
    Just ctx -> check $ typedValidator $ trace "Parsed ScriptContext" ctx

validatorCode :: CompiledCode (BuiltinData -> BuiltinUnit)
validatorCode = $$(compile [||untypedValidator||])

validatorCodeFullyApplied :: CompiledCode BuiltinUnit
validatorCodeFullyApplied =
  validatorCode `unsafeApplyCode` liftCodeDef (toBuiltinData testScriptContext)

----------------------------------------------------------------------------------------
-- Test Fixture ------------------------------------------------------------------------

testScriptContext :: ScriptContext
testScriptContext =
  ScriptContext
    { scriptContextTxInfo = txInfo
    , scriptContextRedeemer
    , scriptContextScriptInfo
    }
 where
  txInfo =
    TxInfo
      { txInfoInputs = mempty
      , txInfoReferenceInputs = mempty
      , txInfoOutputs = mempty
      , txInfoTxCerts = mempty
      , txInfoRedeemers = Map.empty
      , txInfoVotes = Map.empty
      , txInfoProposalProcedures = mempty
      , txInfoCurrentTreasuryAmount = Nothing
      , txInfoTreasuryDonation = Nothing
      , txInfoFee = 0
      , txInfoMint = emptyMintValue
      , txInfoWdrl = Map.empty
      , txInfoValidRange =
          Interval
            (LowerBound (Finite 110) True)
            (UpperBound (Finite 1100) True)
      , txInfoSignatories = List.singleton testBeneficiaryPKH
      , txInfoData = Map.empty
      , txInfoId = "058fdca70be67c74151cea3846be7f73342d92c0090b62c1052e6790ad83f145"
      }

  scriptContextRedeemer :: Redeemer
  scriptContextRedeemer = Redeemer (toBuiltinData FullUnlock)

  scriptContextScriptInfo :: ScriptInfo
  scriptContextScriptInfo =
    SpendingScript (TxOutRef txOutRefId txOutRefIdx) (Just datum)
   where
    txOutRefId = "058fdca70be67c74151cea3846be7f73342d92c0090b62c1052e6790ad83f145"
    txOutRefIdx = 0
    datum :: Datum
    datum = Datum (toBuiltinData testVestingDatum)

testVestingDatum :: VestingDatum
testVestingDatum =
  VestingDatum
    { beneficiary = Address (PubKeyCredential testBeneficiaryPKH) Nothing
    , vestingAsset = assetClass (CurrencySymbol "$") (TokenName "test-asset")
    , totalVestingQty = 1000
    , vestingPeriodStart = 0
    , vestingPeriodEnd = 100
    , firstUnlockPossibleAfter = 10
    , totalInstallments = 10
    }

testBeneficiaryPKH :: PubKeyHash
testBeneficiaryPKH = PubKeyHash ""
