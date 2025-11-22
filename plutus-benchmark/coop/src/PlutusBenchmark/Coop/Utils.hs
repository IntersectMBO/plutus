{-# LANGUAGE NamedFieldPuns    #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications  #-}

module PlutusBenchmark.Coop.Utils where

import PlutusTx.Prelude
import Prelude ()

import PlutusLedgerApi.V1 (Datum (Datum), DatumHash)
import PlutusLedgerApi.V1.Data.Value
import PlutusLedgerApi.V2.Data.Contexts
import PlutusLedgerApi.V2.Data.Tx
import PlutusTx.BuiltinList qualified as BIList
import PlutusTx.Builtins.Internal qualified as BI
import PlutusTx.Data.AssocMap (Map, lookup)
import PlutusTx.Data.AssocMap qualified as AssocMap
import PlutusTx.Data.List (List, find)

findOwnInput' :: List TxInInfo -> TxOutRef -> TxInInfo
findOwnInput' inputs oref =
  case find (\i -> txInInfoOutRef i == oref) inputs of
    Nothing -> traceError "findOwnInput: not found"
    Just x  -> x

mustBurnOwnSingletonValue :: ScriptContext -> BuiltinUnit
mustBurnOwnSingletonValue (ScriptContext (TxInfo {..}) (Spending oref)) =
  let (TxInInfo _ (TxOut {txOutValue = ownInputValue})) = findOwnInput' txInfoInputs oref
  -- flattenValue actually reverses order. See plutus#7173.
  in case flattenValue ownInputValue of
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
        Nothing        -> traceError "expected datum but given datum hash have no associated datum"
        Just (Datum d) -> unsafeFromBuiltinData @a d
    OutputDatum (Datum d) -> unsafeFromBuiltinData @a d
{-# INLINE resolveDatum #-}

currencyValue :: CurrencySymbol -> Value -> Value
currencyValue cs val = withCurrencySymbol cs val mempty (\v -> Value $ AssocMap.singleton cs v)
{-# INLINE currencyValue #-}

unsafeMergeMap :: AssocMap.Map k v -> AssocMap.Map k v -> AssocMap.Map k v
unsafeMergeMap x y = AssocMap.unsafeFromBuiltinList (BIList.append (AssocMap.toBuiltinList x) (AssocMap.toBuiltinList y))
{-# INLINE unsafeMergeMap #-}

hashInput :: TxInInfo -> BuiltinByteString
hashInput (TxInInfo (TxOutRef (TxId hash) idx) _)
  | idx < 256 = blake2b_256 (consByteString idx hash)
  | otherwise = traceError "hashInput: Transaction output index must fit in an octet"
{-# INLINE hashInput #-}

errorIfFalse :: BuiltinString -> Bool -> BuiltinUnit
errorIfFalse msg False = traceError msg
errorIfFalse _ True    = BI.unitval
{-# INLINE errorIfFalse #-}

errorIfTrue :: BuiltinString -> Bool -> BuiltinUnit
errorIfTrue msg True = traceError msg
errorIfTrue _ False  = BI.unitval
{-# INLINE errorIfTrue #-}

hasCurrency :: CurrencySymbol -> Value -> Bool
hasCurrency cs (Value val) = AssocMap.member cs val
{-# INLINE hasCurrency #-}
