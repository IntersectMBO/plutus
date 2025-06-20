{-# LANGUAGE BangPatterns      #-}
{-# LANGUAGE NamedFieldPuns    #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications  #-}
{-# LANGUAGE ViewPatterns      #-}

module PlutusBenchmark.Coop.FsValidator where

import PlutusTx.Prelude
import Prelude ()

import PlutusLedgerApi.V1.Interval
import PlutusLedgerApi.V1.Value
import PlutusLedgerApi.V1.Value qualified as Value
import PlutusLedgerApi.V3
import PlutusLedgerApi.V3.MintValue
import PlutusTx.AssocMap qualified as AssocMap
import PlutusTx.Builtins.Internal qualified as BI
import PlutusTx.List

import PlutusBenchmark.Coop.Types
import PlutusBenchmark.Coop.Utils

fsV :: ScriptContext -> BuiltinUnit
fsV = mustBurnOwnSingletonValue

certV :: ScriptContext -> BuiltinUnit
certV = mustBurnOwnSingletonValue

fsMp :: FsMpParams -> ScriptContext -> BuiltinUnit
fsMp
  _params
  (ScriptContext
   (TxInfo {..})
   (Redeemer (unsafeFromBuiltinData @FsMpRedeemer -> FsMpBurn))
   (MintingScript ownCs)
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
        currencyValue ownCs (mintValueToValue txInfoMint) == allOwnCurrValue
  in BI.unitval
fsMp
  (FsMpParams {fmp'fsVAddress, fmp'authParams = AuthParams {..}})
  (ScriptContext
   (TxInfo {..})
   (Redeemer (unsafeFromBuiltinData @FsMpRedeemer -> FsMpBurn))
   (MintingScript ownCs)
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
            in case find predicate validCerts of
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
            currencyValue ap'authTokenCs (mintValueToValue txInfoMint) == authTokensToBurn
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

             (mayFsTn, unusedAuthInputs') = foldl matchWithAuth (Nothing, mempty) unusedAuthInputs
           in case mayFsTn of
                 Nothing -> traceError "$FS must have a token name formed from a matching $AUTH input"
                 Just fsTn -> (fsToMint' <> Value.singleton ownCs fsTn 1, unusedAuthInputs')

    (fsToMint, restAuths) = foldl go (mempty, validAuthInputs) txInfoOutputs
    !_checkAuthUse = errorIfFalse "Auth inputs must ALL be used" $ null restAuths
    !_checkBurn =
      errorIfFalse "" $
        currencyValue ownCs (mintValueToValue txInfoMint) == fsToMint
  in BI.unitval
fsMp _ _ = traceError "GHC's pattern exhaustiveness checker is being silly, this won't get compiled"
