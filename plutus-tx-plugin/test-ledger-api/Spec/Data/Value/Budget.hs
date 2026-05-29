{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE NoImplicitPrelude #-}

{-|
Budget comparison between the builtin Value lookup ('unsafeDataAsValue' +
'lookupCoin') and the pure Plutus Tx Data-backed Value API ('valueOf')
across a scaling series of Value sizes:

* S1   — ada only (1 token).
* S3   — ada + 2 single-token policies (3 tokens total).
* S8   — ada + 7 single-token policies (8 tokens total); tuned so the builtin
         vs non-builtin CPU ratio at an ada lookup lands near 1:1 — the
         crossover.
* S100 — ada + 10 policies with 10 tokens each (~100 tokens).

Currency symbols are 28 bytes and token names are 32 bytes, matching the
sizes that appear on-chain.

Every bundle starts from a 'BuiltinData' input — the same representation a
validator receives from the ledger — so both paths are exercised on
identical lifted inputs and the only variation is how each unwraps the
'BuiltinData' before operating on it.

The 'unValueData_S*' bundles measure 'unsafeDataAsValue' standalone, so the
conversion tax can be subtracted from the builtin column when reading the
matrix.

See issue IntersectMBO\/plutus-private#2242. -}
module Spec.Data.Value.Budget where

import PlutusTx.Prelude

import PlutusLedgerApi.Test.V1.Data.Value (listsToValue)
import PlutusLedgerApi.V1.Data.Value qualified as DValue
import PlutusTx.Builtins qualified as B
import PlutusTx.Builtins.Internal qualified as BI
import PlutusTx.Code (CompiledCode, unsafeApplyCode)
import PlutusTx.IsData qualified as Tx
import PlutusTx.Lift (liftCodeDef)
import PlutusTx.TH (compile)
import PlutusTx.Test (goldenBundle)
import Test.Tasty (TestTree)
import Test.Tasty.Extras (runTestNested, testNestedGhc)

tests :: TestTree
tests =
  runTestNested ["test-ledger-api", "Spec", "Data", "Value", "Budget"]
    . pure
    . testNestedGhc
    $ [ -- S1: ada-only. Hit on ada, plus a miss.
        goldenBundle
          "lookup_S1_ada_builtin"
          lookupAdaBuiltin
          (lookupAdaBuiltin `unsafeApplyCode` valueS1)
      , goldenBundle
          "lookup_S1_ada_nonbuiltin"
          lookupAdaNonBuiltin
          (lookupAdaNonBuiltin `unsafeApplyCode` valueS1)
      , goldenBundle
          "lookup_S1_miss_builtin"
          lookupMissBuiltin
          (lookupMissBuiltin `unsafeApplyCode` valueS1)
      , goldenBundle
          "lookup_S1_miss_nonbuiltin"
          lookupMissNonBuiltin
          (lookupMissNonBuiltin `unsafeApplyCode` valueS1)
      , goldenBundle
          "lookup_S1_ada_raw"
          lookupAdaRaw
          (lookupAdaRaw `unsafeApplyCode` valueS1)
      , goldenBundle
          "lookup_S1_miss_raw"
          lookupMissRaw
          (lookupMissRaw `unsafeApplyCode` valueS1)
      , -- S3: ada + two single-token policies.
        goldenBundle
          "lookup_S3_ada_builtin"
          lookupAdaBuiltin
          (lookupAdaBuiltin `unsafeApplyCode` valueS3)
      , goldenBundle
          "lookup_S3_ada_nonbuiltin"
          lookupAdaNonBuiltin
          (lookupAdaNonBuiltin `unsafeApplyCode` valueS3)
      , goldenBundle
          "lookup_S3_middle_builtin"
          lookupCs01Tn01Builtin
          (lookupCs01Tn01Builtin `unsafeApplyCode` valueS3)
      , goldenBundle
          "lookup_S3_middle_nonbuiltin"
          lookupCs01Tn01NonBuiltin
          (lookupCs01Tn01NonBuiltin `unsafeApplyCode` valueS3)
      , goldenBundle
          "lookup_S3_last_builtin"
          lookupCs02Tn02Builtin
          (lookupCs02Tn02Builtin `unsafeApplyCode` valueS3)
      , goldenBundle
          "lookup_S3_last_nonbuiltin"
          lookupCs02Tn02NonBuiltin
          (lookupCs02Tn02NonBuiltin `unsafeApplyCode` valueS3)
      , goldenBundle
          "lookup_S3_miss_builtin"
          lookupMissBuiltin
          (lookupMissBuiltin `unsafeApplyCode` valueS3)
      , goldenBundle
          "lookup_S3_miss_nonbuiltin"
          lookupMissNonBuiltin
          (lookupMissNonBuiltin `unsafeApplyCode` valueS3)
      , goldenBundle
          "lookup_S3_ada_raw"
          lookupAdaRaw
          (lookupAdaRaw `unsafeApplyCode` valueS3)
      , goldenBundle
          "lookup_S3_middle_raw"
          lookupCs01Tn01Raw
          (lookupCs01Tn01Raw `unsafeApplyCode` valueS3)
      , goldenBundle
          "lookup_S3_last_raw"
          lookupCs02Tn02Raw
          (lookupCs02Tn02Raw `unsafeApplyCode` valueS3)
      , goldenBundle
          "lookup_S3_miss_raw"
          lookupMissRaw
          (lookupMissRaw `unsafeApplyCode` valueS3)
      , -- S8: ada + 7 single-token policies. Tuned so the builtin/non-builtin
        -- CPU ratio at the "ada hit" position lands near the crossover —
        -- where the 'unsafeDataAsValue' traversal cost has grown to match
        -- the short-circuited 'valueOf' cost for an ada lookup.
        goldenBundle
          "lookup_S8_ada_builtin"
          lookupAdaBuiltin
          (lookupAdaBuiltin `unsafeApplyCode` valueS8)
      , goldenBundle
          "lookup_S8_ada_nonbuiltin"
          lookupAdaNonBuiltin
          (lookupAdaNonBuiltin `unsafeApplyCode` valueS8)
      , goldenBundle
          "lookup_S8_middle_builtin"
          lookupCs04Tn04Builtin
          (lookupCs04Tn04Builtin `unsafeApplyCode` valueS8)
      , goldenBundle
          "lookup_S8_middle_nonbuiltin"
          lookupCs04Tn04NonBuiltin
          (lookupCs04Tn04NonBuiltin `unsafeApplyCode` valueS8)
      , goldenBundle
          "lookup_S8_last_builtin"
          lookupCs07Tn07Builtin
          (lookupCs07Tn07Builtin `unsafeApplyCode` valueS8)
      , goldenBundle
          "lookup_S8_last_nonbuiltin"
          lookupCs07Tn07NonBuiltin
          (lookupCs07Tn07NonBuiltin `unsafeApplyCode` valueS8)
      , goldenBundle
          "lookup_S8_miss_builtin"
          lookupMissBuiltin
          (lookupMissBuiltin `unsafeApplyCode` valueS8)
      , goldenBundle
          "lookup_S8_miss_nonbuiltin"
          lookupMissNonBuiltin
          (lookupMissNonBuiltin `unsafeApplyCode` valueS8)
      , goldenBundle
          "lookup_S8_ada_raw"
          lookupAdaRaw
          (lookupAdaRaw `unsafeApplyCode` valueS8)
      , goldenBundle
          "lookup_S8_middle_raw"
          lookupCs04Tn04Raw
          (lookupCs04Tn04Raw `unsafeApplyCode` valueS8)
      , goldenBundle
          "lookup_S8_last_raw"
          lookupCs07Tn07Raw
          (lookupCs07Tn07Raw `unsafeApplyCode` valueS8)
      , goldenBundle
          "lookup_S8_miss_raw"
          lookupMissRaw
          (lookupMissRaw `unsafeApplyCode` valueS8)
      , -- S100: ada + 10 policies × 10 tokens each.
        goldenBundle
          "lookup_S100_ada_builtin"
          lookupAdaBuiltin
          (lookupAdaBuiltin `unsafeApplyCode` valueS100)
      , goldenBundle
          "lookup_S100_ada_nonbuiltin"
          lookupAdaNonBuiltin
          (lookupAdaNonBuiltin `unsafeApplyCode` valueS100)
      , goldenBundle
          "lookup_S100_middle_builtin"
          lookupCs05Tn05Builtin
          (lookupCs05Tn05Builtin `unsafeApplyCode` valueS100)
      , goldenBundle
          "lookup_S100_middle_nonbuiltin"
          lookupCs05Tn05NonBuiltin
          (lookupCs05Tn05NonBuiltin `unsafeApplyCode` valueS100)
      , goldenBundle
          "lookup_S100_last_builtin"
          lookupCs10Tn10Builtin
          (lookupCs10Tn10Builtin `unsafeApplyCode` valueS100)
      , goldenBundle
          "lookup_S100_last_nonbuiltin"
          lookupCs10Tn10NonBuiltin
          (lookupCs10Tn10NonBuiltin `unsafeApplyCode` valueS100)
      , goldenBundle
          "lookup_S100_miss_builtin"
          lookupMissBuiltin
          (lookupMissBuiltin `unsafeApplyCode` valueS100)
      , goldenBundle
          "lookup_S100_miss_nonbuiltin"
          lookupMissNonBuiltin
          (lookupMissNonBuiltin `unsafeApplyCode` valueS100)
      , goldenBundle
          "lookup_S100_ada_raw"
          lookupAdaRaw
          (lookupAdaRaw `unsafeApplyCode` valueS100)
      , goldenBundle
          "lookup_S100_middle_raw"
          lookupCs05Tn05Raw
          (lookupCs05Tn05Raw `unsafeApplyCode` valueS100)
      , goldenBundle
          "lookup_S100_last_raw"
          lookupCs10Tn10Raw
          (lookupCs10Tn10Raw `unsafeApplyCode` valueS100)
      , goldenBundle
          "lookup_S100_miss_raw"
          lookupMissRaw
          (lookupMissRaw `unsafeApplyCode` valueS100)
      , -- Standalone 'unsafeDataAsValue' per shape. Isolates the conversion
        -- tax from any downstream operation, so the per-shape unwrap
        -- overhead can be read directly.
        goldenBundle
          "unValueData_S1"
          unValueDataOnly
          (unValueDataOnly `unsafeApplyCode` valueS1)
      , goldenBundle
          "unValueData_S3"
          unValueDataOnly
          (unValueDataOnly `unsafeApplyCode` valueS3)
      , goldenBundle
          "unValueData_S8"
          unValueDataOnly
          (unValueDataOnly `unsafeApplyCode` valueS8)
      , goldenBundle
          "unValueData_S100"
          unValueDataOnly
          (unValueDataOnly `unsafeApplyCode` valueS100)
      ]

-- --------------------------------------------------------------------------
-- Raw 28-byte currency-symbol bytes.
-- --------------------------------------------------------------------------

bsPolicyMiss :: BuiltinByteString
bsPolicyMiss = "policy_Miss_________________"
{-# INLINEABLE bsPolicyMiss #-}

bsPolicy01 :: BuiltinByteString
bsPolicy01 = "policy_01___________________"
{-# INLINEABLE bsPolicy01 #-}

bsPolicy02 :: BuiltinByteString
bsPolicy02 = "policy_02___________________"
{-# INLINEABLE bsPolicy02 #-}

bsPolicy03 :: BuiltinByteString
bsPolicy03 = "policy_03___________________"
{-# INLINEABLE bsPolicy03 #-}

bsPolicy04 :: BuiltinByteString
bsPolicy04 = "policy_04___________________"
{-# INLINEABLE bsPolicy04 #-}

bsPolicy05 :: BuiltinByteString
bsPolicy05 = "policy_05___________________"
{-# INLINEABLE bsPolicy05 #-}

bsPolicy06 :: BuiltinByteString
bsPolicy06 = "policy_06___________________"
{-# INLINEABLE bsPolicy06 #-}

bsPolicy07 :: BuiltinByteString
bsPolicy07 = "policy_07___________________"
{-# INLINEABLE bsPolicy07 #-}

bsPolicy08 :: BuiltinByteString
bsPolicy08 = "policy_08___________________"
{-# INLINEABLE bsPolicy08 #-}

bsPolicy09 :: BuiltinByteString
bsPolicy09 = "policy_09___________________"
{-# INLINEABLE bsPolicy09 #-}

bsPolicy10 :: BuiltinByteString
bsPolicy10 = "policy_10___________________"
{-# INLINEABLE bsPolicy10 #-}

-- --------------------------------------------------------------------------
-- Raw 32-byte token-name bytes.
-- --------------------------------------------------------------------------

bsTokMiss :: BuiltinByteString
bsTokMiss = "token_Miss______________________"
{-# INLINEABLE bsTokMiss #-}

bsTok01 :: BuiltinByteString
bsTok01 = "token_01________________________"
{-# INLINEABLE bsTok01 #-}

bsTok02 :: BuiltinByteString
bsTok02 = "token_02________________________"
{-# INLINEABLE bsTok02 #-}

bsTok03 :: BuiltinByteString
bsTok03 = "token_03________________________"
{-# INLINEABLE bsTok03 #-}

bsTok04 :: BuiltinByteString
bsTok04 = "token_04________________________"
{-# INLINEABLE bsTok04 #-}

bsTok05 :: BuiltinByteString
bsTok05 = "token_05________________________"
{-# INLINEABLE bsTok05 #-}

bsTok06 :: BuiltinByteString
bsTok06 = "token_06________________________"
{-# INLINEABLE bsTok06 #-}

bsTok07 :: BuiltinByteString
bsTok07 = "token_07________________________"
{-# INLINEABLE bsTok07 #-}

bsTok08 :: BuiltinByteString
bsTok08 = "token_08________________________"
{-# INLINEABLE bsTok08 #-}

bsTok09 :: BuiltinByteString
bsTok09 = "token_09________________________"
{-# INLINEABLE bsTok09 #-}

bsTok10 :: BuiltinByteString
bsTok10 = "token_10________________________"
{-# INLINEABLE bsTok10 #-}

-- --------------------------------------------------------------------------
-- Typed 'CurrencySymbol' wrappers.
-- --------------------------------------------------------------------------

csPolicyMiss :: DValue.CurrencySymbol
csPolicyMiss = DValue.CurrencySymbol bsPolicyMiss
{-# INLINEABLE csPolicyMiss #-}

cs01 :: DValue.CurrencySymbol
cs01 = DValue.CurrencySymbol bsPolicy01
{-# INLINEABLE cs01 #-}

cs02 :: DValue.CurrencySymbol
cs02 = DValue.CurrencySymbol bsPolicy02
{-# INLINEABLE cs02 #-}

cs03 :: DValue.CurrencySymbol
cs03 = DValue.CurrencySymbol bsPolicy03
{-# INLINEABLE cs03 #-}

cs04 :: DValue.CurrencySymbol
cs04 = DValue.CurrencySymbol bsPolicy04
{-# INLINEABLE cs04 #-}

cs05 :: DValue.CurrencySymbol
cs05 = DValue.CurrencySymbol bsPolicy05
{-# INLINEABLE cs05 #-}

cs06 :: DValue.CurrencySymbol
cs06 = DValue.CurrencySymbol bsPolicy06
{-# INLINEABLE cs06 #-}

cs07 :: DValue.CurrencySymbol
cs07 = DValue.CurrencySymbol bsPolicy07
{-# INLINEABLE cs07 #-}

cs08 :: DValue.CurrencySymbol
cs08 = DValue.CurrencySymbol bsPolicy08
{-# INLINEABLE cs08 #-}

cs09 :: DValue.CurrencySymbol
cs09 = DValue.CurrencySymbol bsPolicy09
{-# INLINEABLE cs09 #-}

cs10 :: DValue.CurrencySymbol
cs10 = DValue.CurrencySymbol bsPolicy10
{-# INLINEABLE cs10 #-}

-- --------------------------------------------------------------------------
-- Typed 'TokenName' wrappers.
-- --------------------------------------------------------------------------

tnMiss :: DValue.TokenName
tnMiss = DValue.TokenName bsTokMiss
{-# INLINEABLE tnMiss #-}

tn01 :: DValue.TokenName
tn01 = DValue.TokenName bsTok01
{-# INLINEABLE tn01 #-}

tn02 :: DValue.TokenName
tn02 = DValue.TokenName bsTok02
{-# INLINEABLE tn02 #-}

tn03 :: DValue.TokenName
tn03 = DValue.TokenName bsTok03
{-# INLINEABLE tn03 #-}

tn04 :: DValue.TokenName
tn04 = DValue.TokenName bsTok04
{-# INLINEABLE tn04 #-}

tn05 :: DValue.TokenName
tn05 = DValue.TokenName bsTok05
{-# INLINEABLE tn05 #-}

tn06 :: DValue.TokenName
tn06 = DValue.TokenName bsTok06
{-# INLINEABLE tn06 #-}

tn07 :: DValue.TokenName
tn07 = DValue.TokenName bsTok07
{-# INLINEABLE tn07 #-}

tn08 :: DValue.TokenName
tn08 = DValue.TokenName bsTok08
{-# INLINEABLE tn08 #-}

tn09 :: DValue.TokenName
tn09 = DValue.TokenName bsTok09
{-# INLINEABLE tn09 #-}

tn10 :: DValue.TokenName
tn10 = DValue.TokenName bsTok10
{-# INLINEABLE tn10 #-}

-- --------------------------------------------------------------------------
-- Haskell-side helper tables for building S100.
-- --------------------------------------------------------------------------

s100Policies :: [DValue.CurrencySymbol]
s100Policies = [cs01, cs02, cs03, cs04, cs05, cs06, cs07, cs08, cs09, cs10]

s100Tokens :: [DValue.TokenName]
s100Tokens = [tn01, tn02, tn03, tn04, tn05, tn06, tn07, tn08, tn09, tn10]

-- --------------------------------------------------------------------------
-- Sample Values encoded as BuiltinData.
-- --------------------------------------------------------------------------

valueS1 :: CompiledCode B.BuiltinData
valueS1 = liftCodeDef . Tx.toBuiltinData $ do
  listsToValue [(DValue.adaSymbol, [(DValue.adaToken, 1000000)])]

valueS3 :: CompiledCode B.BuiltinData
valueS3 = liftCodeDef . Tx.toBuiltinData $ do
  listsToValue
    [ (DValue.adaSymbol, [(DValue.adaToken, 1000000)])
    , (cs01, [(tn01, 42)])
    , (cs02, [(tn02, 7)])
    ]

valueS8 :: CompiledCode B.BuiltinData
valueS8 = liftCodeDef . Tx.toBuiltinData $ do
  listsToValue
    [ (DValue.adaSymbol, [(DValue.adaToken, 1000000)])
    , (cs01, [(tn01, 1)])
    , (cs02, [(tn02, 1)])
    , (cs03, [(tn03, 1)])
    , (cs04, [(tn04, 1)])
    , (cs05, [(tn05, 1)])
    , (cs06, [(tn06, 1)])
    , (cs07, [(tn07, 1)])
    ]

valueS100 :: CompiledCode B.BuiltinData
valueS100 = liftCodeDef . Tx.toBuiltinData $ do
  listsToValue $ (DValue.adaSymbol, [(DValue.adaToken, 1000000)])
    : [(cs, [(tn, 1) | tn <- s100Tokens]) | cs <- s100Policies]

-- --------------------------------------------------------------------------
-- Compiled lookup operations.
--
-- Each pair computes the same logical result from a BuiltinData input:
-- how many units of a given (policy, token) the value contains.
--
-- Builtin path:     BuiltinData -(unsafeDataAsValue)->     BuiltinValue
--                                -(lookupCoin)->          Integer
-- Non-builtin path: BuiltinData -(unsafeFromBuiltinData)-> Value
--                                -(valueOf)->             Integer
-- --------------------------------------------------------------------------

lookupAdaBuiltin :: CompiledCode (B.BuiltinData -> Integer)
lookupAdaBuiltin =
  $$(compile [||\bd -> B.lookupCoin "" "" (B.unsafeDataAsValue bd)||])

lookupAdaNonBuiltin :: CompiledCode (B.BuiltinData -> Integer)
lookupAdaNonBuiltin =
  $$( compile
        [||
        \bd ->
          DValue.valueOf (Tx.unsafeFromBuiltinData bd) DValue.adaSymbol DValue.adaToken
        ||]
    )

lookupMissBuiltin :: CompiledCode (B.BuiltinData -> Integer)
lookupMissBuiltin =
  $$(compile [||\bd -> B.lookupCoin bsPolicyMiss bsTokMiss (B.unsafeDataAsValue bd)||])

lookupMissNonBuiltin :: CompiledCode (B.BuiltinData -> Integer)
lookupMissNonBuiltin =
  $$(compile [||\bd -> DValue.valueOf (Tx.unsafeFromBuiltinData bd) csPolicyMiss tnMiss||])

lookupCs01Tn01Builtin :: CompiledCode (B.BuiltinData -> Integer)
lookupCs01Tn01Builtin =
  $$(compile [||\bd -> B.lookupCoin bsPolicy01 bsTok01 (B.unsafeDataAsValue bd)||])

lookupCs01Tn01NonBuiltin :: CompiledCode (B.BuiltinData -> Integer)
lookupCs01Tn01NonBuiltin =
  $$(compile [||\bd -> DValue.valueOf (Tx.unsafeFromBuiltinData bd) cs01 tn01||])

lookupCs02Tn02Builtin :: CompiledCode (B.BuiltinData -> Integer)
lookupCs02Tn02Builtin =
  $$(compile [||\bd -> B.lookupCoin bsPolicy02 bsTok02 (B.unsafeDataAsValue bd)||])

lookupCs02Tn02NonBuiltin :: CompiledCode (B.BuiltinData -> Integer)
lookupCs02Tn02NonBuiltin =
  $$(compile [||\bd -> DValue.valueOf (Tx.unsafeFromBuiltinData bd) cs02 tn02||])

lookupCs04Tn04Builtin :: CompiledCode (B.BuiltinData -> Integer)
lookupCs04Tn04Builtin =
  $$(compile [||\bd -> B.lookupCoin bsPolicy04 bsTok04 (B.unsafeDataAsValue bd)||])

lookupCs04Tn04NonBuiltin :: CompiledCode (B.BuiltinData -> Integer)
lookupCs04Tn04NonBuiltin =
  $$(compile [||\bd -> DValue.valueOf (Tx.unsafeFromBuiltinData bd) cs04 tn04||])

lookupCs05Tn05Builtin :: CompiledCode (B.BuiltinData -> Integer)
lookupCs05Tn05Builtin =
  $$(compile [||\bd -> B.lookupCoin bsPolicy05 bsTok05 (B.unsafeDataAsValue bd)||])

lookupCs05Tn05NonBuiltin :: CompiledCode (B.BuiltinData -> Integer)
lookupCs05Tn05NonBuiltin =
  $$(compile [||\bd -> DValue.valueOf (Tx.unsafeFromBuiltinData bd) cs05 tn05||])

lookupCs07Tn07Builtin :: CompiledCode (B.BuiltinData -> Integer)
lookupCs07Tn07Builtin =
  $$(compile [||\bd -> B.lookupCoin bsPolicy07 bsTok07 (B.unsafeDataAsValue bd)||])

lookupCs07Tn07NonBuiltin :: CompiledCode (B.BuiltinData -> Integer)
lookupCs07Tn07NonBuiltin =
  $$(compile [||\bd -> DValue.valueOf (Tx.unsafeFromBuiltinData bd) cs07 tn07||])

lookupCs10Tn10Builtin :: CompiledCode (B.BuiltinData -> Integer)
lookupCs10Tn10Builtin =
  $$(compile [||\bd -> B.lookupCoin bsPolicy10 bsTok10 (B.unsafeDataAsValue bd)||])

lookupCs10Tn10NonBuiltin :: CompiledCode (B.BuiltinData -> Integer)
lookupCs10Tn10NonBuiltin =
  $$(compile [||\bd -> DValue.valueOf (Tx.unsafeFromBuiltinData bd) cs10 tn10||])

-- --------------------------------------------------------------------------
-- Raw 'BuiltinData' lookup.
--
-- Walks the BuiltinData-encoded Value directly, taking raw BuiltinByteString
-- keys instead of CurrencySymbol / TokenName newtypes and skipping the
-- 'unsafeFromBuiltinData' tax that the typed 'valueOf' pays at the caller
-- boundary. This is what 'PlutusLedgerApi.V1.Data.Value.valueOf' would look
-- like if it operated on raw BuiltinData; included here as a separate column
-- so the SoP-conversion overhead can be read off the matrix directly.
-- --------------------------------------------------------------------------

valueOfRaw :: B.BuiltinByteString -> B.BuiltinByteString -> B.BuiltinData -> Integer
valueOfRaw cur tn bd = goOuter (BI.unsafeDataAsMap bd)
  where
    goOuter = B.caseList' 0 \hd ->
      if B.equalsByteString cur (BI.unsafeDataAsB (BI.fst hd))
        then \_ -> goInner (BI.unsafeDataAsMap (BI.snd hd))
        else goOuter

    goInner = B.caseList' 0 \hd ->
      if B.equalsByteString tn (BI.unsafeDataAsB (BI.fst hd))
        then \_ -> BI.unsafeDataAsI (BI.snd hd)
        else goInner
{-# INLINEABLE valueOfRaw #-}

lookupAdaRaw :: CompiledCode (B.BuiltinData -> Integer)
lookupAdaRaw = $$(compile [||\bd -> valueOfRaw "" "" bd||])

lookupMissRaw :: CompiledCode (B.BuiltinData -> Integer)
lookupMissRaw = $$(compile [||\bd -> valueOfRaw bsPolicyMiss bsTokMiss bd||])

lookupCs01Tn01Raw :: CompiledCode (B.BuiltinData -> Integer)
lookupCs01Tn01Raw = $$(compile [||\bd -> valueOfRaw bsPolicy01 bsTok01 bd||])

lookupCs02Tn02Raw :: CompiledCode (B.BuiltinData -> Integer)
lookupCs02Tn02Raw = $$(compile [||\bd -> valueOfRaw bsPolicy02 bsTok02 bd||])

lookupCs04Tn04Raw :: CompiledCode (B.BuiltinData -> Integer)
lookupCs04Tn04Raw = $$(compile [||\bd -> valueOfRaw bsPolicy04 bsTok04 bd||])

lookupCs05Tn05Raw :: CompiledCode (B.BuiltinData -> Integer)
lookupCs05Tn05Raw = $$(compile [||\bd -> valueOfRaw bsPolicy05 bsTok05 bd||])

lookupCs07Tn07Raw :: CompiledCode (B.BuiltinData -> Integer)
lookupCs07Tn07Raw = $$(compile [||\bd -> valueOfRaw bsPolicy07 bsTok07 bd||])

lookupCs10Tn10Raw :: CompiledCode (B.BuiltinData -> Integer)
lookupCs10Tn10Raw = $$(compile [||\bd -> valueOfRaw bsPolicy10 bsTok10 bd||])

-- --------------------------------------------------------------------------
-- Standalone 'unsafeDataAsValue' measurement.
--
-- Isolates the conversion cost from any downstream operation, so the
-- per-shape unwrap overhead can be subtracted from the builtin column
-- when reading the matrix.
-- --------------------------------------------------------------------------

unValueDataOnly :: CompiledCode (B.BuiltinData -> BI.BuiltinValue)
unValueDataOnly =
  $$(compile [||\bd -> B.unsafeDataAsValue bd||])
