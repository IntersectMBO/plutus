{-# LANGUAGE BangPatterns      #-}
{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE NamedFieldPuns    #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE TypeApplications  #-}
{-# LANGUAGE ViewPatterns      #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:datatypes=BuiltinCasing #-}

module PlutusBenchmark.Coop.Scripts where

import PlutusTx
import PlutusTx.Plugin ()
import PlutusTx.Prelude
import Prelude ()

import PlutusLedgerApi.Data.V2
import PlutusLedgerApi.V1.Data.Interval (contains)
import PlutusLedgerApi.V1.Data.Value (isZero, unAssetClass, valueOf, withCurrencySymbol)
import PlutusLedgerApi.V1.Data.Value qualified as Value

import PlutusTx.Builtins qualified as Builtins
import PlutusTx.Builtins.Internal qualified as BI
import PlutusTx.Data.AssocMap qualified as AssocMap
import PlutusTx.Data.List (elem, foldl)
import PlutusTx.List qualified as BIList

import PlutusBenchmark.Coop.Types
import PlutusBenchmark.Coop.Utils

fsV :: CompiledCode (Datum -> BuiltinData -> BuiltinData -> BuiltinUnit)
fsV = $$(compile [|| \_ _ sc -> mustBurnOwnSingletonValue (unsafeFromBuiltinData sc) ||])

certV :: CompiledCode (Datum -> BuiltinData -> BuiltinData -> BuiltinUnit)
certV = $$(compile [|| \_ _ sc -> mustBurnOwnSingletonValue (unsafeFromBuiltinData sc) ||])

fsMp :: CompiledCode (FsMpParams -> BuiltinData -> BuiltinData -> BuiltinUnit)
fsMp = $$(compile [|| \p r sc -> fsMp' p (unsafeFromBuiltinData r) (unsafeFromBuiltinData sc) ||])

authMp :: CompiledCode (AuthMpParams -> BuiltinData -> BuiltinData -> BuiltinUnit)
authMp = $$(compile [|| \p r sc -> authMp' p (unsafeFromBuiltinData r) (unsafeFromBuiltinData sc) ||])

certMp :: CompiledCode (CertMpParams -> BuiltinData -> BuiltinData -> BuiltinUnit)
certMp = $$(compile [|| \p r sc -> certMp' p (unsafeFromBuiltinData r) (unsafeFromBuiltinData sc) ||])

fsMp' :: FsMpParams -> FsMpRedeemer -> ScriptContext -> BuiltinUnit
fsMp'
  _params
  FsMpBurn
  (ScriptContext
   (TxInfo {..})
   (Minting ownCs)
  ) =
  let
    go acc (TxInInfo _ (TxOut {..})) =
      let ownCurrValue = withCurrencySymbol ownCs txOutValue AssocMap.empty id
      in if AssocMap.null ownCurrValue
         then acc
         else
           let
             (FsDatum {..}) = resolveDatum @FsDatum txInfoData txOutDatum
             !_checkSignature =
               errorIfFalse "submitter must sign" $
                 elem fs'submitter txInfoSignatories
             !_checkRange =
               errorIfFalse "valid range is correct" $
                 contains
                   (Interval (LowerBound fs'gcAfter False) (UpperBound PosInf True))
                   txInfoValidRange
           in unsafeMergeMap acc ownCurrValue

    allOwnCurrValue = negate $ Value $ AssocMap.singleton ownCs (foldl go AssocMap.empty txInfoInputs)
    !_checkBurn =
      errorIfFalse "" $
        currencyValue ownCs txInfoMint == allOwnCurrValue
  in BI.unitval
fsMp'
  (FsMpParams {fmp'fsVAddress, fmp'authParams = AuthParams {..}})
  FsMpMint
  (ScriptContext
   (TxInfo {..})
   (Minting ownCs)
  ) =
  let
    validCerts =
      let
        go' acc (TxInInfo _ (TxOut {txOutDatum = txInDat, txOutValue = txInVal})) =
          let certVal = currencyValue ap'certTokenCs txInVal
          in if certVal == mempty
             then acc
             else
               let
                 certDat@(CertDatum {..}) = resolveDatum @CertDatum txInfoData txInDat
                 !_checkTokenName =
                   errorIfFalse "$CERT token name must match CertDatum ID" $
                     valueOf certVal ap'certTokenCs (TokenName $ getLedgerBytes cert'id) == 1
                 !_checkRange =
                   errorIfFalse "cert is invalid" $
                     contains cert'validity txInfoValidRange
               in certDat : acc

      in foldl go' mempty txInfoReferenceInputs

    validAuthInputs =
      let
        go' acc@(validAuthInputs'', shouldBeBurned) txIn@(TxInInfo _ (TxOut {txOutValue = txInVal})) =
          if hasCurrency ap'authTokenCs txInVal
          then
            let
              predicate (CertDatum {..}) =
                0 < valueOf txInVal ap'authTokenCs (TokenName $ getLedgerBytes cert'id)
            in case BIList.find predicate validCerts of
              Nothing -> traceError "$AUTH must be validated with a $CERT"
              Just (CertDatum {..}) ->
                let
                  shouldbeBurned' =
                    shouldBeBurned
                    <> Value.singleton ap'authTokenCs (TokenName $ getLedgerBytes cert'id) (-1)
                in (txIn : validAuthInputs'', shouldbeBurned')
          else acc

        (validAuthInputs', authTokensToBurn) = foldl go' (mempty, mempty) txInfoInputs
        !_checkBurn =
          errorIfFalse "" $
            currencyValue ap'authTokenCs txInfoMint == authTokensToBurn
      in validAuthInputs'

    go acc@(fsToMint', unusedAuthInputs) (TxOut {..}) =
      let ownCurrValue = withCurrencySymbol ownCs txOutValue AssocMap.empty id
      in if AssocMap.null ownCurrValue
         then acc
         else
           let
             !_checkDatum = resolveDatum @FsDatum txInfoData txOutDatum
             !_checkAddress =
               errorIfFalse "minted value is not sent to correct address" $
               fmp'fsVAddress == txOutAddress

             matchWithAuth (Nothing, unusedAuthInputs'') authInput =
               let
                 fsTokenName :: TokenName
                 fsTokenName = TokenName $ hashInput authInput
               in if (Value $ AssocMap.singleton ownCs ownCurrValue)
                     == Value.singleton ownCs fsTokenName 1
                  then (Just fsTokenName, unusedAuthInputs'')
                  else (Nothing, authInput : unusedAuthInputs'')
             matchWithAuth (myFsTn', unusedAuthInputs'') authInput =
               (myFsTn', (authInput : unusedAuthInputs''))

             (mayFsTn, unusedAuthInputs') = BIList.foldl matchWithAuth (Nothing, mempty) unusedAuthInputs
           in case mayFsTn of
                 Nothing -> traceError "$FS must have a token name formed from a matching $AUTH input"
                 Just fsTn -> (fsToMint' <> Value.singleton ownCs fsTn 1, unusedAuthInputs')

    (fsToMint, restAuths) = foldl go (mempty, validAuthInputs) txInfoOutputs
    !_checkAuthUse = errorIfFalse "Auth inputs must ALL be used" $ BIList.null restAuths
    !_checkBurn =
      errorIfFalse "" $
        currencyValue ownCs txInfoMint == fsToMint
  in BI.unitval
fsMp' _ _ _ = traceError "incorrect purpose"
{-# INLINE fsMp' #-}

authMp' :: AuthMpParams -> AuthMpRedeemer -> ScriptContext -> BuiltinUnit
authMp'
  _
  AuthMpBurn
  (ScriptContext
   (TxInfo {..})
   (Minting ownCs)
  ) =
  let
    ownValue = currencyValue ownCs txInfoMint
  in errorIfTrue "Own value $AUTH in txMint must all be burned" (isZero ownValue)
authMp'
  (AuthMpParams {..})
  AuthMpMint
  (ScriptContext
   (TxInfo {..})
   (Minting ownCs)
  ) =
  let
    (aaCs, aaTn) = unAssetClass amp'authAuthorityAc
    go
      acc
      (TxInInfo (TxOutRef {txOutRefId = txId, txOutRefIdx = txIdx}) (TxOut {txOutValue = txInVal})) =
        if hasCurrency aaCs txInVal
        then
          let
            (aaVal, tnBytes) = acc
            tnBytes' = tnBytes <> (consByteString txIdx (getTxId txId))
            aaVal' = aaVal + valueOf txInVal aaCs aaTn
          in (aaVal', tnBytes')
        else acc
    authId =
      let
        (aaTokensSpent, tnBytes) = foldl go (0, mempty) txInfoInputs
      in
        if amp'requiredAtLeastAaQ <= aaTokensSpent
        then blake2b_256 tnBytes
        else traceError "Must spend at least the specified amount of AA tokens"

  in case AssocMap.lookup ownCs (getValue txInfoMint) of
       Nothing ->
         traceError $
           "Must mint at least one $AUTH token:\n"
           <> "Must have a specified CurrencySymbol in the Value"
       Just tokenNameMap ->
         let
           (kv, rest) = Builtins.unsafeUncons (AssocMap.toBuiltinList tokenNameMap)
           k = BI.unsafeDataAsB $ BI.fst kv
           v = BI.unsafeDataAsI $ BI.snd kv
         in errorIfFalse "Must mint at least one $AUTH token" (0 < v && BI.null rest && k == authId)
authMp' _ _ _ = traceError "incorrect purpose"
{-# INLINE authMp' #-}

certMp' :: CertMpParams -> CertMpRedeemer -> ScriptContext -> BuiltinUnit
certMp'
  (CertMpParams {..})
  CertMpMint
  (ScriptContext
   (TxInfo {..})
   (Minting ownCs)
  ) =
  let
    tnBytes =
      let
        (aaCs, aaTn) = unAssetClass cmp'authAuthorityAc
        go acc@(aaVal, tnBytes'') (TxInInfo (TxOutRef {txOutRefId = txId, txOutRefIdx = txIdx}) (TxOut {txOutValue = txInVal})) =
          if hasCurrency aaCs txInVal
          then (aaVal + valueOf txInVal aaCs aaTn, tnBytes'' <> consByteString txIdx (getTxId txId))
          else acc
        (aaTokensSpent, tnBytes') = foldl go (0, mempty) txInfoInputs
      in if cmp'requiredAtLeastAaQ <= aaTokensSpent
         then blake2b_256 tnBytes'
         else traceError "Must spend at least the specified amount of AA tokens"
    certTn = TokenName tnBytes
    !_mustMintCert =
      errorIfFalse
      "Must mint 1 $CERT"
      (currencyValue ownCs txInfoMint == (Value.singleton ownCs certTn 1))

    !_mustPayCurrencyWithDatum =
      let
        go paid (TxOut {txOutValue = val, txOutAddress = address, txOutDatum = dat}) =
          if address == cmp'certVAddress
          then
            let
              (CertDatum {..}) = resolveDatum @CertDatum txInfoData dat
            in
              if (getLedgerBytes cert'id) == tnBytes
              then paid + (currencyValue ownCs val)
              else traceError "Must attach a valid datum"
          else paid
        paidVal = foldl go mempty txInfoOutputs
      in errorIfFalse "Must pay the specific value" (paidVal == Value.singleton ownCs certTn 1)
  in BI.unitval

certMp'
  _
  CertMpBurn
  (ScriptContext
   (TxInfo {..})
   (Minting ownCs)
  ) =
  let
    inputSum =
      foldl (\acc (TxInInfo _ (TxOut {txOutValue})) -> acc + txOutValue) mempty txInfoInputs
    go shouldBurn' (TxInInfo _ (TxOut {txOutValue = txInVal, txOutDatum = txOutDatum})) =
      if hasCurrency ownCs txInVal
      then
        let
          (CertDatum {..}) = resolveDatum @CertDatum txInfoData txOutDatum
          UpperBound certValidUntil _ = ivTo cert'validity
          !_checkRange =
            contains
            (Interval (LowerBound certValidUntil False) (UpperBound PosInf True))
            txInfoValidRange
          (redeemerCs, redeemerName) = unAssetClass cert'redeemerAc
          !_spendAtLeast =
            errorIfFalse
              "Not have at least one token specified by redeemer spent"
              (valueOf inputSum redeemerCs redeemerName >= 1)
          certVal = Value.singleton ownCs (TokenName $ getLedgerBytes cert'id) 1
          !_mustSpendOneCERTToken =
            errorIfFalse
              "Must spend one $CERT token"
              (currencyValue ownCs txInVal == certVal)
        in shouldBurn' + (inv certVal)
      else shouldBurn'
    shouldBurn = foldl go mempty txInfoInputs
    !_mustMintCurrency =
      errorIfFalse
        "Must mint specified value of currency"
        (currencyValue ownCs txInfoMint == shouldBurn)
  in BI.unitval
certMp' _ _ _ = traceError "incorrect purpose"
{-# INLINE certMp' #-}
