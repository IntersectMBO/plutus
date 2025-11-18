{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:datatypes=BuiltinCasing #-}

module PlutusBenchmark.V1.Data.ScriptContexts where

import PlutusLedgerApi.Data.V1
import PlutusLedgerApi.V1.Data.Address
import PlutusLedgerApi.V1.Data.Value
import PlutusTx qualified
import PlutusTx.Builtins qualified as PlutusTx
import PlutusTx.Data.List qualified as Data.List
import PlutusTx.Plugin ()
import PlutusTx.Prelude qualified as PlutusTx

{-| A very crude deterministic generator for 'ScriptContext's with size
approximately proportional to the input integer. -}
mkScriptContext :: Integer -> ScriptContext
mkScriptContext i =
  ScriptContext
    (mkTxInfo i)
    (Spending (TxOutRef (TxId "") 0))

mkTxInfo :: Integer -> TxInfo
mkTxInfo i =
  TxInfo
    { txInfoInputs = mempty
    , txInfoOutputs = Data.List.map mkTxOut (Data.List.fromSOP ([1 .. i] :: [Integer]))
    , txInfoFee = mempty
    , txInfoMint = mempty
    , txInfoDCert = mempty
    , txInfoWdrl = mempty
    , txInfoValidRange = always
    , txInfoSignatories = mempty
    , txInfoData = mempty
    , txInfoId = TxId ""
    }

mkTxOut :: Integer -> TxOut
mkTxOut i =
  TxOut
    { txOutAddress = pubKeyHashAddress (PubKeyHash "")
    , txOutValue = mkValue i
    , txOutDatumHash = Nothing
    }

mkValue :: Integer -> Value
mkValue i = assetClassValue (assetClass adaSymbol adaToken) i

-- This example decodes the script context (which is O(size-of-context) work), and then also
-- does some work that's roughly proportional to the size of the script context (counting the
-- outputs). This should be a somewhat realistic example where a reasonable chunk of work is
-- done in addition to decoding.
checkScriptContext1 :: PlutusTx.BuiltinData -> ()
checkScriptContext1 d =
  -- Bang pattern to ensure this is forced, probably not necesssary
  -- since we do use it later
  let !sc = PlutusTx.unsafeFromBuiltinData d
      ScriptContext txi _ = sc
   in if Data.List.length (txInfoOutputs txi) `PlutusTx.modInteger` 2 PlutusTx.== 0
        then ()
        else PlutusTx.traceError "Odd number of outputs"
{-# INLINEABLE checkScriptContext1 #-}

mkCheckScriptContext1Code :: ScriptContext -> PlutusTx.CompiledCode ()
mkCheckScriptContext1Code sc =
  let d = PlutusTx.toBuiltinData sc
   in $$(PlutusTx.compile [||checkScriptContext1||])
        `PlutusTx.unsafeApplyCode` PlutusTx.liftCodeDef d

-- This example aims to *force* the decoding of the script context and then ignore it entirely.
-- This corresponds to the unfortunate case where the decoding "wrapper" around a script forces
-- all the decoding work to be done even if it isn't used.
checkScriptContext2 :: PlutusTx.BuiltinData -> ()
checkScriptContext2 d =
  let (sc :: ScriptContext) = PlutusTx.unsafeFromBuiltinData d
   in -- Just using a bang pattern was not enough to stop GHC from getting
      -- rid of the dead binding before we even hit the plugin, this works
      -- for now!
      case sc of
        !_ ->
          if 48 PlutusTx.* 9900 PlutusTx.== (475200 :: Integer)
            then ()
            else PlutusTx.traceError "Got my sums wrong"
{-# INLINEABLE checkScriptContext2 #-}

mkCheckScriptContext2Code :: ScriptContext -> PlutusTx.CompiledCode ()
mkCheckScriptContext2Code sc =
  let d = PlutusTx.toBuiltinData sc
   in $$(PlutusTx.compile [||checkScriptContext2||])
        `PlutusTx.unsafeApplyCode` PlutusTx.liftCodeDef d

{- Note [Redundant arguments to equality benchmarks]
The arguments for the benchmarks are passed as terms created with `liftCodeDef`.
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
scriptContextEqualityData :: ScriptContext -> PlutusTx.BuiltinData -> ()
-- See Note [Redundant arguments to equality benchmarks]
scriptContextEqualityData _ d =
  if PlutusTx.equalsData d d
    then ()
    else PlutusTx.traceError "The argument is not equal to itself"
{-# INLINEABLE scriptContextEqualityData #-}

mkScriptContextEqualityDataCode :: ScriptContext -> PlutusTx.CompiledCode ()
mkScriptContextEqualityDataCode sc =
  let d = PlutusTx.toBuiltinData sc
   in $$(PlutusTx.compile [||scriptContextEqualityData||])
        `PlutusTx.unsafeApplyCode` PlutusTx.liftCodeDef sc
        `PlutusTx.unsafeApplyCode` PlutusTx.liftCodeDef d

-- This example is just the overhead from the previous two
-- See Note [Redundant arguments to equality benchmarks]
scriptContextEqualityOverhead :: ScriptContext -> PlutusTx.BuiltinData -> ()
scriptContextEqualityOverhead _ _ = ()
{-# INLINEABLE scriptContextEqualityOverhead #-}

mkScriptContextEqualityOverheadCode :: ScriptContext -> PlutusTx.CompiledCode ()
mkScriptContextEqualityOverheadCode sc =
  let d = PlutusTx.toBuiltinData sc
   in $$(PlutusTx.compile [||scriptContextEqualityOverhead||])
        `PlutusTx.unsafeApplyCode` PlutusTx.liftCodeDef sc
        `PlutusTx.unsafeApplyCode` PlutusTx.liftCodeDef d
