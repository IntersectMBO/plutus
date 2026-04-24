{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE NoImplicitPrelude #-}

{-|
Budget comparison between the builtin Value ops ('unsafeDataAsValue',
'lookupCoin', 'unionValue') and the pure Plutus Tx Data-backed Value API
('valueOf', 'unionWith') across a scaling series of Value sizes:

* S1   — ada only (1 token).
* S3   — ada + 2 single-token policies (3 tokens total).
* S8   — ada + 7 single-token policies (8 tokens total); tuned so the builtin
         vs non-builtin CPU ratio at an ada lookup is near 1:1 — the crossover.
* S100 — ada + 10 policies with 10 tokens each (~100 tokens).

Currency symbols are 28 bytes and token names are 32 bytes, matching the
sizes that appear on-chain.

Every bundle starts from a 'BuiltinData' input — the same representation a
validator receives from the ledger — so the two paths are exercised on
identical lifted inputs and the only variation is how each unwraps the
'BuiltinData' before operating on it.

See issue IntersectMBO\/plutus-private#2177. -}
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
          "lookup_S1_ada_handrolled"
          lookupAdaHandrolled
          (lookupAdaHandrolled `unsafeApplyCode` valueS1)
      , goldenBundle
          "lookup_S1_miss_handrolled"
          lookupMissHandrolled
          (lookupMissHandrolled `unsafeApplyCode` valueS1)
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
          "lookup_S3_ada_handrolled"
          lookupAdaHandrolled
          (lookupAdaHandrolled `unsafeApplyCode` valueS3)
      , goldenBundle
          "lookup_S3_middle_handrolled"
          lookupCs01Tn01Handrolled
          (lookupCs01Tn01Handrolled `unsafeApplyCode` valueS3)
      , goldenBundle
          "lookup_S3_last_handrolled"
          lookupCs02Tn02Handrolled
          (lookupCs02Tn02Handrolled `unsafeApplyCode` valueS3)
      , goldenBundle
          "lookup_S3_miss_handrolled"
          lookupMissHandrolled
          (lookupMissHandrolled `unsafeApplyCode` valueS3)
      , -- S8: ada + 7 single-token policies. Tuned so the builtin/non-builtin
        -- CPU ratio at the "ada hit" position lands near 1:1 — this is the
        -- crossover scenario, where the `unsafeDataAsValue` traversal cost has
        -- grown to match the short-circuited `valueOf` cost for an ada lookup.
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
          "lookup_S8_ada_handrolled"
          lookupAdaHandrolled
          (lookupAdaHandrolled `unsafeApplyCode` valueS8)
      , goldenBundle
          "lookup_S8_middle_handrolled"
          lookupCs04Tn04Handrolled
          (lookupCs04Tn04Handrolled `unsafeApplyCode` valueS8)
      , goldenBundle
          "lookup_S8_last_handrolled"
          lookupCs07Tn07Handrolled
          (lookupCs07Tn07Handrolled `unsafeApplyCode` valueS8)
      , goldenBundle
          "lookup_S8_miss_handrolled"
          lookupMissHandrolled
          (lookupMissHandrolled `unsafeApplyCode` valueS8)
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
          "lookup_S100_ada_handrolled"
          lookupAdaHandrolled
          (lookupAdaHandrolled `unsafeApplyCode` valueS100)
      , goldenBundle
          "lookup_S100_middle_handrolled"
          lookupCs05Tn05Handrolled
          (lookupCs05Tn05Handrolled `unsafeApplyCode` valueS100)
      , goldenBundle
          "lookup_S100_last_handrolled"
          lookupCs10Tn10Handrolled
          (lookupCs10Tn10Handrolled `unsafeApplyCode` valueS100)
      , goldenBundle
          "lookup_S100_miss_handrolled"
          lookupMissHandrolled
          (lookupMissHandrolled `unsafeApplyCode` valueS100)
      , -- Union-and-lookup: combine two copies of each shape and inspect
        -- ada in the result. Conservation-of-value pattern.
        goldenBundle
          "union_S1_builtin"
          unionAdaBuiltin
          (unionAdaBuiltin `unsafeApplyCode` valueS1 `unsafeApplyCode` valueS1)
      , goldenBundle
          "union_S1_nonbuiltin"
          unionAdaNonBuiltin
          (unionAdaNonBuiltin `unsafeApplyCode` valueS1 `unsafeApplyCode` valueS1)
      , goldenBundle
          "union_S3_builtin"
          unionAdaBuiltin
          (unionAdaBuiltin `unsafeApplyCode` valueS3 `unsafeApplyCode` valueS3)
      , goldenBundle
          "union_S3_nonbuiltin"
          unionAdaNonBuiltin
          (unionAdaNonBuiltin `unsafeApplyCode` valueS3 `unsafeApplyCode` valueS3)
      , goldenBundle
          "union_S8_builtin"
          unionAdaBuiltin
          (unionAdaBuiltin `unsafeApplyCode` valueS8 `unsafeApplyCode` valueS8)
      , goldenBundle
          "union_S8_nonbuiltin"
          unionAdaNonBuiltin
          (unionAdaNonBuiltin `unsafeApplyCode` valueS8 `unsafeApplyCode` valueS8)
      , goldenBundle
          "union_S100_builtin"
          unionAdaBuiltin
          (unionAdaBuiltin `unsafeApplyCode` valueS100 `unsafeApplyCode` valueS100)
      , goldenBundle
          "union_S100_nonbuiltin"
          unionAdaNonBuiltin
          (unionAdaNonBuiltin `unsafeApplyCode` valueS100 `unsafeApplyCode` valueS100)
      , goldenBundle
          "union_S1_handrolled"
          unionAdaHandrolled
          (unionAdaHandrolled `unsafeApplyCode` valueS1 `unsafeApplyCode` valueS1)
      , goldenBundle
          "union_S3_handrolled"
          unionAdaHandrolled
          (unionAdaHandrolled `unsafeApplyCode` valueS3 `unsafeApplyCode` valueS3)
      , goldenBundle
          "union_S8_handrolled"
          unionAdaHandrolled
          (unionAdaHandrolled `unsafeApplyCode` valueS8 `unsafeApplyCode` valueS8)
      , goldenBundle
          "union_S100_handrolled"
          unionAdaHandrolled
          (unionAdaHandrolled `unsafeApplyCode` valueS100 `unsafeApplyCode` valueS100)
      , -- Standalone `unsafeDataAsValue` per shape. Isolates the conversion
        -- tax from downstream ops.
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
-- Hand-rolled helpers operating directly on raw BuiltinData.
--
-- These bypass the CurrencySymbol / TokenName newtype wrappers and the
-- Maybe / withCurrencySymbol continuation indirection that PlutusLedgerApi's
-- `valueOf` chains together. The union variant additionally exploits the
-- ledger invariant that output Values have strictly positive quantities,
-- so it skips the zero-filter that `unionWith` does via the `These` algebra.
-- --------------------------------------------------------------------------

-- | Look up a key in a Data-encoded map, short-circuiting on first match.
lookupKeyInMap
  :: B.BuiltinData
  -> BI.BuiltinList (BI.BuiltinPair B.BuiltinData B.BuiltinData)
  -> Maybe B.BuiltinData
lookupKeyInMap k = go
  where
    go = B.caseList' Nothing \hd ->
      if B.equalsData k (BI.fst hd)
        then \_ -> Just (BI.snd hd)
        else go
{-# INLINEABLE lookupKeyInMap #-}

-- | Return 'True' if a key appears in a Data-encoded map.
containsKeyInMap
  :: B.BuiltinData
  -> BI.BuiltinList (BI.BuiltinPair B.BuiltinData B.BuiltinData)
  -> Bool
containsKeyInMap k = go
  where
    go = B.caseList' False \hd ->
      if B.equalsData k (BI.fst hd)
        then \_ -> True
        else go
{-# INLINEABLE containsKeyInMap #-}

-- | Append two BuiltinLists.
appendBuiltinList
  :: forall a
   . BI.BuiltinList a
  -> BI.BuiltinList a
  -> BI.BuiltinList a
appendBuiltinList l1 l2 = go l1
  where
    go =
      B.caseList'
        l2
        (\hd tl -> BI.mkCons hd (go tl))
{-# INLINEABLE appendBuiltinList #-}

{-| Look up the integer quantity for a (currency, token) pair directly from
a 'BuiltinData'-encoded 'Value'. Returns 0 if either key is missing.

This replicates what `valueOf` does semantically but without going through
`CurrencySymbol`/`TokenName` newtype wrappers, `AssocMap.lookup`'s
`Maybe`-wrapping, or `withCurrencySymbol`'s continuation. -}
handRolledLookup :: B.BuiltinData -> BuiltinByteString -> BuiltinByteString -> Integer
handRolledLookup bd cs tn = goOuter (BI.unsafeDataAsMap bd)
  where
    goOuter = B.caseList' 0 \hd ->
      if B.equalsByteString cs (BI.unsafeDataAsB (BI.fst hd))
        then \_ -> goInner (BI.unsafeDataAsMap (BI.snd hd))
        else goOuter

    goInner = B.caseList' 0 \hd ->
      if B.equalsByteString tn (BI.unsafeDataAsB (BI.fst hd))
        then \_ -> BI.unsafeDataAsI (BI.snd hd)
        else goInner
{-# INLINEABLE handRolledLookup #-}

{-| Union two 'BuiltinData'-encoded 'Value's. Produces a new 'BuiltinData'.
Assumes all quantities are strictly positive (ledger invariant for Values
from tx outputs), so it does not filter out zero entries. -}
handRolledUnion :: B.BuiltinData -> B.BuiltinData -> B.BuiltinData
handRolledUnion bd1 bd2 =
  let outer1 = BI.unsafeDataAsMap bd1
      outer2 = BI.unsafeDataAsMap bd2
   in BI.mkMap (appendBuiltinList (mergeOuters outer1 outer2) (filterMissingOuter outer2 outer1))
  where
    mergeOuters l1 l2 = goOuter l1
      where
        goOuter =
          B.caseList' (BI.mkNilPairData BI.unitval) \hd ->
            let csData = BI.fst hd
                inner1 = BI.snd hd
                mergedValue = case lookupKeyInMap csData l2 of
                  Just inner2Data ->
                    let i1 = BI.unsafeDataAsMap inner1
                        i2 = BI.unsafeDataAsMap inner2Data
                     in BI.mkMap (appendBuiltinList (mergeInners i1 i2) (filterMissingOuter i2 i1))
                  Nothing -> inner1
             in \tl -> BI.mkCons (BI.mkPairData csData mergedValue) (goOuter tl)

    mergeInners l1 l2 = goInner l1
      where
        goInner =
          B.caseList' (BI.mkNilPairData BI.unitval) \hd ->
            let tnData = BI.fst hd
                amt1 = BI.unsafeDataAsI (BI.snd hd)
                combined = case lookupKeyInMap tnData l2 of
                  Just amt2Data -> amt1 + BI.unsafeDataAsI amt2Data
                  Nothing -> amt1
             in \tl ->
                  BI.mkCons
                    (BI.mkPairData tnData (BI.mkI combined))
                    (goInner tl)

    -- Keep entries from l2 whose key is NOT in l1.
    filterMissingOuter l2 l1 = go l2
      where
        go = B.caseList' (BI.mkNilPairData BI.unitval) \hd ->
          if containsKeyInMap (BI.fst hd) l1
            then \tl -> go tl
            else \tl -> BI.mkCons hd (go tl)
{-# INLINEABLE handRolledUnion #-}

-- --------------------------------------------------------------------------
-- Compiled hand-rolled lookup operations.
-- --------------------------------------------------------------------------

lookupAdaHandrolled :: CompiledCode (B.BuiltinData -> Integer)
lookupAdaHandrolled =
  $$(compile [||\bd -> handRolledLookup bd "" ""||])

lookupMissHandrolled :: CompiledCode (B.BuiltinData -> Integer)
lookupMissHandrolled =
  $$(compile [||\bd -> handRolledLookup bd bsPolicyMiss bsTokMiss||])

lookupCs01Tn01Handrolled :: CompiledCode (B.BuiltinData -> Integer)
lookupCs01Tn01Handrolled =
  $$(compile [||\bd -> handRolledLookup bd bsPolicy01 bsTok01||])

lookupCs02Tn02Handrolled :: CompiledCode (B.BuiltinData -> Integer)
lookupCs02Tn02Handrolled =
  $$(compile [||\bd -> handRolledLookup bd bsPolicy02 bsTok02||])

lookupCs04Tn04Handrolled :: CompiledCode (B.BuiltinData -> Integer)
lookupCs04Tn04Handrolled =
  $$(compile [||\bd -> handRolledLookup bd bsPolicy04 bsTok04||])

lookupCs05Tn05Handrolled :: CompiledCode (B.BuiltinData -> Integer)
lookupCs05Tn05Handrolled =
  $$(compile [||\bd -> handRolledLookup bd bsPolicy05 bsTok05||])

lookupCs07Tn07Handrolled :: CompiledCode (B.BuiltinData -> Integer)
lookupCs07Tn07Handrolled =
  $$(compile [||\bd -> handRolledLookup bd bsPolicy07 bsTok07||])

lookupCs10Tn10Handrolled :: CompiledCode (B.BuiltinData -> Integer)
lookupCs10Tn10Handrolled =
  $$(compile [||\bd -> handRolledLookup bd bsPolicy10 bsTok10||])

-- --------------------------------------------------------------------------
-- Compiled union-and-lookup operations.
--
-- Combine two incoming BuiltinData-encoded values and inspect how much ada
-- the result contains. This is the conservation-of-value pattern from the
-- issue: validators union the values from their inputs and outputs and
-- then compare specific coins.
-- --------------------------------------------------------------------------

unionAdaBuiltin :: CompiledCode (B.BuiltinData -> B.BuiltinData -> Integer)
unionAdaBuiltin =
  $$( compile
        [||
        \bd1 bd2 ->
          B.lookupCoin
            ""
            ""
            (B.unionValue (B.unsafeDataAsValue bd1) (B.unsafeDataAsValue bd2))
        ||]
    )

unionAdaNonBuiltin :: CompiledCode (B.BuiltinData -> B.BuiltinData -> Integer)
unionAdaNonBuiltin =
  $$( compile
        [||
        \bd1 bd2 ->
          DValue.valueOf
            ( DValue.unionWith
                (+)
                (Tx.unsafeFromBuiltinData bd1)
                (Tx.unsafeFromBuiltinData bd2)
            )
            DValue.adaSymbol
            DValue.adaToken
        ||]
    )

{-| Hand-rolled union (materializes a new BuiltinData), then hand-rolled ada lookup.
Exploits the positive-quantities invariant. -}
unionAdaHandrolled :: CompiledCode (B.BuiltinData -> B.BuiltinData -> Integer)
unionAdaHandrolled =
  $$( compile
        [||
        \bd1 bd2 ->
          handRolledLookup (handRolledUnion bd1 bd2) "" ""
        ||]
    )

-- --------------------------------------------------------------------------
-- Standalone `unsafeDataAsValue` measurement.
--
-- Isolates the conversion cost from any downstream operation, so the
-- per-shape `unValueData` overhead can be read directly.
-- --------------------------------------------------------------------------

unValueDataOnly :: CompiledCode (B.BuiltinData -> BI.BuiltinValue)
unValueDataOnly =
  $$(compile [||\bd -> B.unsafeDataAsValue bd||])
