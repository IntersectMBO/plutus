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
  in $$(PlutusTx.compile [|| checkScriptContext1 ||]) `PlutusTx.unsafeApplyCode` PlutusTx.liftCode d

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
  in $$(PlutusTx.compile [|| checkScriptContext2 ||]) `PlutusTx.unsafeApplyCode` PlutusTx.liftCode d

{- Note [Redundant arguments to equality benchmarks]
The arguments for the benchmarks are passed as terms created with `liftCode`.
But the benchmark still needs to _evaluate_ these terms, which adds overhead that
distracts from the main point.

We can't easily remove the overhead, but we can at least include it in both cases to
make things fairer. Hence we include redundant arguments in the two cases to ensure
the same work is done in both cases. There is a third case that is just this overhead
for comparison.
-}

-- This example checks the script context for equality (with itself) when encoded as `Data`.
-- That means it just takes a single builtin call, which is fast (so long as the builtin is
-- costed cheaply).
{-# INLINABLE scriptContextEqualityData #-}
scriptContextEqualityData :: ScriptContext -> PlutusTx.BuiltinData -> ()
-- See note [Redundant arguments to equality benchmarks]
scriptContextEqualityData _ d =
  if PlutusTx.equalsData d d
  then ()
  else PlutusTx.traceError "The argument is not equal to itself"

mkScriptContextEqualityDataCode :: ScriptContext -> PlutusTx.CompiledCode ()
mkScriptContextEqualityDataCode sc =
  let d = PlutusTx.toBuiltinData sc
  in $$(PlutusTx.compile [|| scriptContextEqualityData ||])
    `PlutusTx.unsafeApplyCode` PlutusTx.liftCode sc
    `PlutusTx.unsafeApplyCode` PlutusTx.liftCode d

-- This example checks the script context for equality (with itself) when encoded
-- as a normal (i.e. Scott-encoded) term, using the normal (i.e. typeclass-based) equality
-- functions. This can be quite expensive for a large structure!
{-# INLINABLE scriptContextEqualityTerm #-}
scriptContextEqualityTerm :: ScriptContext -> PlutusTx.BuiltinData -> ()
-- See note [Redundant arguments to equality benchmarks]
scriptContextEqualityTerm sc _ =
  if sc PlutusTx.== sc
  then ()
  else PlutusTx.traceError "The argument is not equal to itself"

mkScriptContextEqualityTermCode :: ScriptContext -> PlutusTx.CompiledCode ()
mkScriptContextEqualityTermCode sc =
  let d = PlutusTx.toBuiltinData sc
  in $$(PlutusTx.compile [|| scriptContextEqualityTerm ||])
    `PlutusTx.unsafeApplyCode` PlutusTx.liftCode sc
    `PlutusTx.unsafeApplyCode` PlutusTx.liftCode d

-- This example is just the overhead from the previous two
-- See note [Redundant arguments to equality benchmarks]
{-# INLINABLE scriptContextEqualityOverhead #-}
scriptContextEqualityOverhead :: ScriptContext -> PlutusTx.BuiltinData -> ()
scriptContextEqualityOverhead _ _ = ()

mkScriptContextEqualityOverheadCode :: ScriptContext -> PlutusTx.CompiledCode ()
mkScriptContextEqualityOverheadCode sc =
  let d = PlutusTx.toBuiltinData sc
  in $$(PlutusTx.compile [|| scriptContextEqualityOverhead ||])
    `PlutusTx.unsafeApplyCode` PlutusTx.liftCode sc
    `PlutusTx.unsafeApplyCode` PlutusTx.liftCode d
