{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}

module PlutusBenchmark.Coop.Utils where

import PlutusTx.Prelude
import Prelude ()

import PlutusLedgerApi.V1.Value (Value (Value), flattenValue, valueOf, withCurrencySymbol)
import PlutusLedgerApi.V2
  ( CurrencySymbol
  , Datum (Datum)
  , DatumHash
  , OutputDatum (NoOutputDatum, OutputDatum, OutputDatumHash)
  , ScriptContext (ScriptContext)
  , ScriptPurpose (Spending)
  , TxId (TxId)
  , TxInInfo (TxInInfo, txInInfoOutRef)
  , TxInfo (TxInfo, txInfoInputs, txInfoMint)
  , TxOut (TxOut, txOutValue)
  , TxOutRef (TxOutRef)
  )
import PlutusTx.AssocMap (Map, lookup)
import PlutusTx.AssocMap qualified as AssocMap
import PlutusTx.Builtins.Internal qualified as BI
import PlutusTx.List (find)

findOwnInput :: [TxInInfo] -> TxOutRef -> TxInInfo
findOwnInput inputs oref =
  case find (\i -> txInInfoOutRef i == oref) inputs of
    Nothing -> traceError "findOwnInput: not found"
    Just x -> x

mustBurnOwnSingletonValue :: ScriptContext -> BuiltinUnit
mustBurnOwnSingletonValue (ScriptContext (TxInfo {..}) (Spending oref)) =
  let (TxInInfo _ (TxOut {txOutValue = ownInputValue})) = findOwnInput txInfoInputs oref
   in -- flattenValue actually reverses order. See plutus#7173.
      case flattenValue ownInputValue of
        [(cs, tk, q), _ada] ->
          if negate (valueOf txInfoMint cs tk) == q
            then BI.unitval
            else traceError "Must burn the all of the single asset this utxo was holding"
        _ -> traceError "The UTXO should exactly have one assets besides Lovelace"
mustBurnOwnSingletonValue _ = traceError "Only spending purpose is supported"
{-# INLINE mustBurnOwnSingletonValue #-}

resolveDatum :: forall a. UnsafeFromData a => Map DatumHash Datum -> OutputDatum -> a
resolveDatum datums outputDatum =
  case outputDatum of
    NoOutputDatum -> traceError "expected datum but got no datum"
    OutputDatumHash hash ->
      case lookup hash datums of
        Nothing -> traceError "expected datum but given datum hash have no associated datum"
        Just (Datum d) -> unsafeFromBuiltinData @a d
    OutputDatum (Datum d) -> unsafeFromBuiltinData @a d

currencyValue :: CurrencySymbol -> Value -> Value
currencyValue cs val = withCurrencySymbol cs val mempty (\v -> Value $ AssocMap.singleton cs v)

unsafeMergeMap :: AssocMap.Map k v -> AssocMap.Map k v -> AssocMap.Map k v
unsafeMergeMap x y = AssocMap.unsafeFromList (AssocMap.toList x <> AssocMap.toList y)

hashInput :: TxInInfo -> BuiltinByteString
hashInput (TxInInfo (TxOutRef (TxId hash) idx) _)
  | idx < 256 = blake2b_256 (consByteString idx hash)
  | otherwise = traceError "hashInput: Transaction output index must fit in an octet"

errorIfFalse :: BuiltinString -> Bool -> BuiltinUnit
errorIfFalse msg False = traceError msg
errorIfFalse _ True = BI.unitval

errorIfTrue :: BuiltinString -> Bool -> BuiltinUnit
errorIfTrue msg True = traceError msg
errorIfTrue _ False = BI.unitval

hasCurrency :: CurrencySymbol -> Value -> Bool
hasCurrency cs (Value val) = AssocMap.member cs val
