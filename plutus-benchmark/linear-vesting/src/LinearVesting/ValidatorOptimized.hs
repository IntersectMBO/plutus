{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
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

module LinearVesting.ValidatorOptimized where

import PlutusTx (CompiledCode, compile)
import PlutusTx.Bool (Bool (..), not, otherwise)
import PlutusTx.Builtins.HasOpaque ()
import PlutusTx.Builtins.Internal qualified as BI
import PlutusTx.Trace (traceError)

{-# INLINE divCeil #-}
divCeil :: BI.BuiltinInteger -> BI.BuiltinInteger -> BI.BuiltinInteger
divCeil x y = BI.addInteger 1 (BI.divideInteger (BI.subtractInteger x 1) y)

{-# INLINE lowerInclusiveTime #-}
lowerInclusiveTime :: BI.BuiltinData -> BI.BuiltinInteger
lowerInclusiveTime iv =
  let ivFields = BI.snd (BI.unsafeDataAsConstr iv)
      lower = BI.head ivFields
      !lowerFields = BI.snd (BI.unsafeDataAsConstr lower)
      extended = BI.head lowerFields
      closureData = BI.head (BI.tail lowerFields)
      closureTag = BI.fst (BI.unsafeDataAsConstr closureData)
      !extCon = BI.unsafeDataAsConstr extended
      extTag = BI.fst extCon
      extFields = BI.snd extCon
      offset =
        if BI.equalsInteger closureTag 1 then 0 else 1
   in if BI.equalsInteger extTag 1
        then BI.addInteger (BI.unsafeDataAsI (BI.head extFields)) offset
        else traceError "Time range not Finite"

{-# INLINE txSignedByOptimized #-}
txSignedByOptimized :: BI.BuiltinList BI.BuiltinData -> BI.BuiltinByteString -> Bool
txSignedByOptimized signatories pkh =
  BI.caseList'
    False
    ( \s ss ->
        let sBytes = BI.unsafeDataAsB s
         in if BI.equalsByteString sBytes pkh
              then True
              else txSignedByOptimized ss pkh
    )
    signatories

{-# INLINE findInputByOutRef #-}
findInputByOutRef :: BI.BuiltinData -> BI.BuiltinList BI.BuiltinData -> BI.BuiltinData
findInputByOutRef ref inputs =
  BI.caseList'
    (traceError "Own input not found")
    ( \txIn txIns ->
        let txInFields = BI.snd (BI.unsafeDataAsConstr txIn)
            txInRef = BI.head txInFields
         in if BI.equalsData txInRef ref
              then txIn
              else findInputByOutRef ref txIns
    )
    inputs

{-# INLINE findOutputByAddress #-}
findOutputByAddress :: BI.BuiltinData -> BI.BuiltinList BI.BuiltinData -> BI.BuiltinData
findOutputByAddress addr outputs =
  BI.caseList'
    (traceError "Own output not found")
    ( \out outs ->
        let outFields = BI.snd (BI.unsafeDataAsConstr out)
            outAddr = BI.head outFields
         in if BI.equalsData outAddr addr
              then out
              else findOutputByAddress addr outs
    )
    outputs

{-# INLINE countInputsAtScript #-}
countInputsAtScript :: BI.BuiltinByteString -> BI.BuiltinList BI.BuiltinData -> BI.BuiltinInteger
countInputsAtScript scriptHash inputs =
  BI.caseList'
    0
    ( \txIn txIns ->
        let txInFields = BI.snd (BI.unsafeDataAsConstr txIn)
            resolvedOut = BI.head (BI.tail txInFields)
            resolvedFields = BI.snd (BI.unsafeDataAsConstr resolvedOut)
            addr = BI.head resolvedFields
            addrFields = BI.snd (BI.unsafeDataAsConstr addr)
            cred = BI.head addrFields
            !credCon = BI.unsafeDataAsConstr cred
            credTag = BI.fst credCon
            credFields = BI.snd credCon
            rest = countInputsAtScript scriptHash txIns
         in if BI.equalsInteger credTag 1
              then
                let vh = BI.unsafeDataAsB (BI.head credFields)
                 in if BI.equalsByteString vh scriptHash
                      then BI.addInteger 1 rest
                      else rest
              else rest
    )
    inputs

{-# INLINE valueOf #-}
valueOf :: BI.BuiltinData -> BI.BuiltinByteString -> BI.BuiltinByteString -> BI.BuiltinInteger
valueOf valueData cs tn =
  let outer = BI.unsafeDataAsMap valueData
   in findCurrency outer
  where
    findCurrency :: BI.BuiltinList (BI.BuiltinPair BI.BuiltinData BI.BuiltinData) -> BI.BuiltinInteger
    findCurrency pairs =
      if BI.null pairs
        then 0
        else
          let pair = BI.head pairs
              key = BI.unsafeDataAsB (BI.fst pair)
           in if BI.equalsByteString key cs
                then findToken (BI.unsafeDataAsMap (BI.snd pair))
                else findCurrency (BI.tail pairs)

    findToken :: BI.BuiltinList (BI.BuiltinPair BI.BuiltinData BI.BuiltinData) -> BI.BuiltinInteger
    findToken pairs =
      if BI.null pairs
        then 0
        else
          let pair = BI.head pairs
              key = BI.unsafeDataAsB (BI.fst pair)
           in if BI.equalsByteString key tn
                then BI.unsafeDataAsI (BI.snd pair)
                else findToken (BI.tail pairs)

{-# INLINE getScriptHashFromAddress #-}
getScriptHashFromAddress :: BI.BuiltinData -> BI.BuiltinByteString
getScriptHashFromAddress addr =
  let addrFields = BI.snd (BI.unsafeDataAsConstr addr)
      cred = BI.head addrFields
      !credCon = BI.unsafeDataAsConstr cred
      credTag = BI.fst credCon
      credFields = BI.snd credCon
   in if BI.equalsInteger credTag 1
        then BI.unsafeDataAsB (BI.head credFields)
        else traceError "Expected ScriptCredential"

{-# INLINE getPubKeyHashFromAddress #-}
getPubKeyHashFromAddress :: BI.BuiltinData -> BI.BuiltinByteString
getPubKeyHashFromAddress addr =
  let addrFields = BI.snd (BI.unsafeDataAsConstr addr)
      cred = BI.head addrFields
      !credCon = BI.unsafeDataAsConstr cred
      credTag = BI.fst credCon
      credFields = BI.snd credCon
   in if BI.equalsInteger credTag 0
        then BI.unsafeDataAsB (BI.head credFields)
        else traceError "Expected PubKeyCredential"

{-# INLINE getSpendingInfo #-}
getSpendingInfo :: BI.BuiltinData -> BI.BuiltinPair BI.BuiltinData BI.BuiltinData
getSpendingInfo scriptInfo =
  let con = BI.unsafeDataAsConstr scriptInfo
      tag = BI.fst con
      fields = BI.snd con
   in if BI.equalsInteger tag 1
        then
          let ownRef = BI.head fields
              maybeDatum = BI.head (BI.tail fields)
              !mdCon = BI.unsafeDataAsConstr maybeDatum
              mdTag = BI.fst mdCon
              mdFields = BI.snd mdCon
           in if BI.equalsInteger mdTag 0
                then BI.mkPairData ownRef (BI.head mdFields)
                else traceError "Missing datum"
        else traceError "Not spending script"

{-# INLINE validateVestingPartialUnlockOptimized #-}
validateVestingPartialUnlockOptimized
  :: BI.BuiltinList BI.BuiltinData
  -> BI.BuiltinList BI.BuiltinData
  -> BI.BuiltinData
  -> BI.BuiltinList BI.BuiltinData
  -> BI.BuiltinData
  -> BI.BuiltinData
  -> Bool
validateVestingPartialUnlockOptimized txInputs txOutputs txValidRange txSignatories ownRef vestingDatum =
  let ownInput = findInputByOutRef ownRef txInputs
      ownInputFields = BI.snd (BI.unsafeDataAsConstr ownInput)
      resolvedOut = BI.head (BI.tail ownInputFields)
      !resolvedFields = BI.snd (BI.unsafeDataAsConstr resolvedOut)
      !inputAddress = BI.head resolvedFields

      scriptHash = getScriptHashFromAddress inputAddress
      ownOutput = findOutputByAddress inputAddress txOutputs
      !ownOutputFields = BI.snd (BI.unsafeDataAsConstr ownOutput)
      outputDatum = BI.head (BI.tail (BI.tail ownOutputFields))

      resolvedDatum = BI.head (BI.tail (BI.tail resolvedFields))

      vdFields = BI.snd (BI.unsafeDataAsConstr vestingDatum)
      vdFields1 = BI.tail vdFields
      !vdFields2 = BI.tail vdFields1
      !vdFields3 = BI.tail vdFields2
      !vdFields4 = BI.tail vdFields3
      !vdFields5 = BI.tail vdFields4
      !vdFields6 = BI.tail vdFields5

      beneficiaryAddr = BI.head vdFields
      assetClassData = BI.head vdFields1
      totalVestingQty = BI.unsafeDataAsI (BI.head vdFields2)
      vestingPeriodStart = BI.unsafeDataAsI (BI.head vdFields3)
      vestingPeriodEnd = BI.unsafeDataAsI (BI.head vdFields4)
      firstUnlockPossibleAfter = BI.unsafeDataAsI (BI.head vdFields5)
      totalInstallments = BI.unsafeDataAsI (BI.head vdFields6)

      assetCon = BI.unsafeDataAsConstr assetClassData
      assetFields = BI.snd assetCon
      assetCs = BI.unsafeDataAsB (BI.head assetFields)
      assetTn = BI.unsafeDataAsB (BI.head (BI.tail assetFields))

      oldRemainingQty = valueOf (BI.head (BI.tail resolvedFields)) assetCs assetTn
      newRemainingQty = valueOf (BI.head (BI.tail ownOutputFields)) assetCs assetTn

      vestingPeriodLength = BI.subtractInteger vestingPeriodEnd vestingPeriodStart
      currentTimeApproximation = lowerInclusiveTime txValidRange
      vestingTimeRemaining = BI.subtractInteger vestingPeriodEnd currentTimeApproximation
      timeBetweenTwoInstallments = divCeil vestingPeriodLength totalInstallments
      futureInstallments = divCeil vestingTimeRemaining timeBetweenTwoInstallments
      expectedRemainingQty =
        divCeil (BI.multiplyInteger futureInstallments totalVestingQty) totalInstallments

      beneficiaryHash = getPubKeyHashFromAddress beneficiaryAddr
      signed = txSignedByOptimized txSignatories beneficiaryHash
   in if
        | not signed ->
            traceError "Missing beneficiary signature"
        | BI.lessThanEqualsInteger currentTimeApproximation firstUnlockPossibleAfter ->
            traceError "Unlock not permitted until firstUnlockPossibleAfter time"
        | BI.lessThanEqualsInteger newRemainingQty 0 ->
            traceError "Zero remaining assets not allowed"
        | BI.lessThanEqualsInteger oldRemainingQty newRemainingQty ->
            traceError "Remaining asset is not decreasing"
        | not (BI.equalsInteger expectedRemainingQty newRemainingQty) ->
            traceError "Mismatched remaining asset"
        | not (BI.equalsData resolvedDatum outputDatum) ->
            traceError "Datum Modification Prohibited"
        | not (BI.equalsInteger (countInputsAtScript scriptHash txInputs) 1) ->
            traceError "Double satisfaction"
        | otherwise -> True

{-# INLINE validateVestingFullUnlockOptimized #-}
validateVestingFullUnlockOptimized
  :: BI.BuiltinData
  -> BI.BuiltinList BI.BuiltinData
  -> BI.BuiltinData
  -> Bool
validateVestingFullUnlockOptimized txValidRange txSignatories vestingDatum =
  let !vdFields = BI.snd (BI.unsafeDataAsConstr vestingDatum)
      vdFields1 = BI.tail vdFields
      vdFields2 = BI.tail vdFields1
      vdFields3 = BI.tail vdFields2
      vdFields4 = BI.tail vdFields3

      beneficiaryAddr = BI.head vdFields
      vestingPeriodEnd = BI.unsafeDataAsI (BI.head vdFields4)
      currentTimeApproximation = lowerInclusiveTime txValidRange
      beneficiaryHash = getPubKeyHashFromAddress beneficiaryAddr
   in if
        | not (txSignedByOptimized txSignatories beneficiaryHash) ->
            traceError "Missing beneficiary signature"
        | BI.lessThanEqualsInteger currentTimeApproximation vestingPeriodEnd ->
            traceError "Unlock not permitted until vestingPeriodEnd time"
        | otherwise -> True

{-# INLINEABLE untypedValidatorOptimized #-}
untypedValidatorOptimized :: BI.BuiltinData -> BI.BuiltinUnit
untypedValidatorOptimized scriptContextData =
  let ctx = BI.trace "Parsing ScriptContext..." scriptContextData
      ctxFields = BI.snd (BI.unsafeDataAsConstr ctx)
      txInfoData = BI.head ctxFields
      redeemerData = BI.head (BI.tail ctxFields)
      scriptInfoData = BI.head (BI.tail (BI.tail ctxFields))

      txInfoFields = BI.snd (BI.unsafeDataAsConstr txInfoData)
      txInfoFields1 = BI.tail txInfoFields
      txInfoFields2 = BI.tail txInfoFields1
      txInfoFields3 = BI.tail txInfoFields2
      txInfoFields4 = BI.tail txInfoFields3
      txInfoFields5 = BI.tail txInfoFields4
      txInfoFields6 = BI.tail txInfoFields5
      txInfoFields7 = BI.tail txInfoFields6
      txInfoFields8 = BI.tail txInfoFields7

      txInputs = BI.unsafeDataAsList (BI.head txInfoFields)
      txOutputs = BI.unsafeDataAsList (BI.head txInfoFields2)
      txValidRange = BI.head txInfoFields7
      txSignatories = BI.unsafeDataAsList (BI.head txInfoFields8)

      spendingInfo = getSpendingInfo scriptInfoData
      ownRef = BI.fst spendingInfo
      datumData = BI.snd spendingInfo

      redeemerTag = BI.fst (BI.unsafeDataAsConstr redeemerData)

      result =
        BI.trace
          "Parsed ScriptContext"
          ( BI.trace
              "Parsed Redeemer"
              ( BI.caseInteger
                  redeemerTag
                  [ BI.trace
                      "Partial unlock requested"
                      ( validateVestingPartialUnlockOptimized
                          txInputs
                          txOutputs
                          txValidRange
                          txSignatories
                          ownRef
                          datumData
                      )
                  , BI.trace
                      "Full unlock requested"
                      (validateVestingFullUnlockOptimized txValidRange txSignatories datumData)
                  ]
              )
          )
   in if result
        then BI.trace "Validation completed" BI.unitval
        else traceError "Validation failed"

validatorOptimizedCode :: CompiledCode (BI.BuiltinData -> BI.BuiltinUnit)
validatorOptimizedCode = $$(compile [||untypedValidatorOptimized||])
