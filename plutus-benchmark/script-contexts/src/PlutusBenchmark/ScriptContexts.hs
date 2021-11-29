{-# LANGUAGE BangPatterns      #-}
{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell   #-}

module PlutusBenchmark.ScriptContexts where

import PlutusLedgerApi.V1
import PlutusLedgerApi.V1.Address
import PlutusLedgerApi.V1.Value
import PlutusTx qualified as PlutusTx
import PlutusTx.Builtins qualified as PlutusTx
import PlutusTx.Code qualified as PlutusTx
import PlutusTx.LiftU qualified as PlutusTx
import PlutusTx.Prelude qualified as PlutusTx

-- | A very crude deterministic generator for 'ScriptContext's with size
-- approximately proportional to the input integer.
mkScriptContext :: Int -> ScriptContext
mkScriptContext i = ScriptContext (mkTxInfo i) (Spending (TxOutRef (TxId "") 0))

mkTxInfo :: Int -> TxInfo
mkTxInfo i = TxInfo {
  txInfoInputs=mempty,
  txInfoOutputs=fmap mkTxOut [1..i],
  txInfoFee=mempty,
  txInfoMint=mempty,
  txInfoDCert=mempty,
  txInfoWdrl=mempty,
  txInfoValidRange=always,
  txInfoSignatories=mempty,
  txInfoData=mempty,
  txInfoId=TxId ""
  }

mkTxOut :: Int -> TxOut
mkTxOut i = TxOut {
  txOutAddress=pubKeyHashAddress (PubKeyHash ""),
  txOutValue=mkValue i,
  txOutDatumHash=Nothing
  }

mkValue :: Int -> Value
mkValue i = assetClassValue (assetClass adaSymbol adaToken) (fromIntegral i)

-- This example decodes the script context (which is O(size-of-context) work), and then also
-- does some work that's roughly proportional to the size of the script context (counting the
-- outputs). This should be a somewhat realistic example where a reasonable chunk of work is
-- done in addition to decoding.
{-# INLINABLE checkScriptContext1 #-}
checkScriptContext1 :: PlutusTx.BuiltinData -> ()
checkScriptContext1 d =
  -- Bang pattern to ensure this is forced, probably not necesssary
  -- since we do use it later
  let !sc = PlutusTx.unsafeFromBuiltinData d
      (ScriptContext txi _) = sc
  in
  if PlutusTx.length (txInfoOutputs txi) `PlutusTx.modInteger` 2 PlutusTx.== 0
  then ()
  else PlutusTx.traceError "Odd number of outputs"

mkCheckScriptContext1Code :: ScriptContext -> PlutusTx.CompiledCode ()
mkCheckScriptContext1Code sc =
  let d = PlutusTx.toBuiltinData sc
  in $$(PlutusTx.compile [|| checkScriptContext1 ||]) `PlutusTx.applyCode` PlutusTx.liftCode d

-- This example aims to *force* the decoding of the script context and then ignore it entirely.
-- This corresponds to the unfortunate case where the decoding "wrapper" around a script forces
-- all the decoding work to be done even if it isn't used.
{-# INLINABLE checkScriptContext2 #-}
checkScriptContext2 :: PlutusTx.BuiltinData -> ()
checkScriptContext2 d =
  let (sc :: ScriptContext) = PlutusTx.unsafeFromBuiltinData d
  -- Just using a bang pattern was not enough to stop GHC from getting
  -- rid of the dead binding before we even hit the plugin, this works
  -- for now!
  in case sc of
    !_ ->
      if 48*9900 PlutusTx.== (475200 :: Integer)
      then ()
      else PlutusTx.traceError "Got my sums wrong"

mkCheckScriptContext2Code :: ScriptContext -> PlutusTx.CompiledCode ()
mkCheckScriptContext2Code sc =
  let d = PlutusTx.toBuiltinData sc
  in $$(PlutusTx.compile [|| checkScriptContext2 ||]) `PlutusTx.applyCode` PlutusTx.liftCode d

-- Same as checkScriptContext1, but passing the ScriptContext as a term using LiftU
{-# INLINABLE checkScriptContext3 #-}
checkScriptContext3 :: ScriptContext -> ()
checkScriptContext3 (ScriptContext txi _) =
  if PlutusTx.length (txInfoOutputs txi) `PlutusTx.modInteger` 2 PlutusTx.== 0
  then ()
  else PlutusTx.traceError "Odd number of outputs"

mkCheckScriptContext3Code :: ScriptContext -> PlutusTx.CompiledCode ()
mkCheckScriptContext3Code sc =
  let d = PlutusTx.liftProgramDef sc
  in $$(PlutusTx.compile [|| checkScriptContext3 ||])
      `PlutusTx.applyCode` PlutusTx.DeserializedCode d Nothing mempty

-- Same as checkScriptContext2, but passing the ScriptContext as a term using LiftU
{-# INLINABLE checkScriptContext4 #-}
checkScriptContext4 :: ScriptContext -> ()
checkScriptContext4 sc =
  case sc of
    !_ ->
      if 48*9900 PlutusTx.== (475200 :: Integer)
      then ()
      else PlutusTx.traceError "Got my sums wrong"

mkCheckScriptContext4Code :: ScriptContext -> PlutusTx.CompiledCode ()
mkCheckScriptContext4Code sc =
  let d = PlutusTx.liftProgramDef sc
  in $$(PlutusTx.compile [|| checkScriptContext4 ||])
      `PlutusTx.applyCode` PlutusTx.DeserializedCode d Nothing mempty
