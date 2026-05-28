{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE NoImplicitPrelude #-}

{-|
Budget comparison between the on-chain builtin union path
('unsafeDataAsValue' + 'unionValue' + 'mkValue') and a hand-rolled
sorted-merge over the raw 'BuiltinData' representation.

* S1   — ada only (1 token).
* S3   — ada + 2 single-token policies (3 tokens total).
* S8   — ada + 7 single-token policies (8 tokens total).
* S100 — ada + 10 policies with 10 tokens each (~101 tokens).

Currency symbols are 28 bytes and token names are 32 bytes, matching the
sizes that appear on-chain.

The bundle pattern is 'BuiltinData' -> 'BuiltinData' -> 'BuiltinData' --
the union is the only operation measured; no downstream 'valueOf' or
'lookupCoin' is folded into the cost.

The raw 'unionValuePositiveRaw' is a Plinth translation of Philip's
'pvalueUnionFast' (Plutarch). It is a sorted-merge with a three-way
branch on key comparison and assumes both inputs are sorted by
lexicographic key (ada ('') first, then policy_01..policy_10) and that
the inner-pair values are strictly positive integers, so the inner sum
never produces a zero that would need filtering. Both 'valueS1', 'valueS3',
'valueS8', 'valueS100' below satisfy these preconditions. -}
module Spec.Data.Value.UnionBudget where

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
  runTestNested ["test-ledger-api", "Spec", "Data", "Value", "UnionBudget"]
    . pure
    . testNestedGhc
    $ [ goldenBundle
          "union_S1_builtin"
          unionValueBuiltinRaw
          (unionValueBuiltinRaw `unsafeApplyCode` valueS1 `unsafeApplyCode` valueS1)
      , goldenBundle
          "union_S1_raw"
          unionValuePositiveRaw
          (unionValuePositiveRaw `unsafeApplyCode` valueS1 `unsafeApplyCode` valueS1)
      , goldenBundle
          "union_S3_builtin"
          unionValueBuiltinRaw
          (unionValueBuiltinRaw `unsafeApplyCode` valueS3 `unsafeApplyCode` valueS3)
      , goldenBundle
          "union_S3_raw"
          unionValuePositiveRaw
          (unionValuePositiveRaw `unsafeApplyCode` valueS3 `unsafeApplyCode` valueS3)
      , goldenBundle
          "union_S8_builtin"
          unionValueBuiltinRaw
          (unionValueBuiltinRaw `unsafeApplyCode` valueS8 `unsafeApplyCode` valueS8)
      , goldenBundle
          "union_S8_raw"
          unionValuePositiveRaw
          (unionValuePositiveRaw `unsafeApplyCode` valueS8 `unsafeApplyCode` valueS8)
      , goldenBundle
          "union_S100_builtin"
          unionValueBuiltinRaw
          (unionValueBuiltinRaw `unsafeApplyCode` valueS100 `unsafeApplyCode` valueS100)
      , goldenBundle
          "union_S100_raw"
          unionValuePositiveRaw
          (unionValuePositiveRaw `unsafeApplyCode` valueS100 `unsafeApplyCode` valueS100)
      ]

-- --------------------------------------------------------------------------
-- Raw 28-byte currency-symbol bytes.
-- --------------------------------------------------------------------------

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
-- Typed wrappers.
-- --------------------------------------------------------------------------

cs01, cs02, cs03, cs04, cs05, cs06, cs07, cs08, cs09, cs10 :: DValue.CurrencySymbol
cs01 = DValue.CurrencySymbol bsPolicy01
cs02 = DValue.CurrencySymbol bsPolicy02
cs03 = DValue.CurrencySymbol bsPolicy03
cs04 = DValue.CurrencySymbol bsPolicy04
cs05 = DValue.CurrencySymbol bsPolicy05
cs06 = DValue.CurrencySymbol bsPolicy06
cs07 = DValue.CurrencySymbol bsPolicy07
cs08 = DValue.CurrencySymbol bsPolicy08
cs09 = DValue.CurrencySymbol bsPolicy09
cs10 = DValue.CurrencySymbol bsPolicy10

tn01, tn02, tn03, tn04, tn05, tn06, tn07, tn08, tn09, tn10 :: DValue.TokenName
tn01 = DValue.TokenName bsTok01
tn02 = DValue.TokenName bsTok02
tn03 = DValue.TokenName bsTok03
tn04 = DValue.TokenName bsTok04
tn05 = DValue.TokenName bsTok05
tn06 = DValue.TokenName bsTok06
tn07 = DValue.TokenName bsTok07
tn08 = DValue.TokenName bsTok08
tn09 = DValue.TokenName bsTok09
tn10 = DValue.TokenName bsTok10

s100Policies :: [DValue.CurrencySymbol]
s100Policies = [cs01, cs02, cs03, cs04, cs05, cs06, cs07, cs08, cs09, cs10]

s100Tokens :: [DValue.TokenName]
s100Tokens = [tn01, tn02, tn03, tn04, tn05, tn06, tn07, tn08, tn09, tn10]

-- --------------------------------------------------------------------------
-- Sample Values encoded as BuiltinData. Keys are kept sorted by construction:
-- ada ('') comes first, then policy_01..policy_10 in lexicographic order.
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
  listsToValue
    $ (DValue.adaSymbol, [(DValue.adaToken, 1000000)])
    : [(cs, [(tn, 1) | tn <- s100Tokens]) | cs <- s100Policies]

-- --------------------------------------------------------------------------
-- Builtin column.
-- --------------------------------------------------------------------------

unionValueBuiltinRaw :: CompiledCode (B.BuiltinData -> B.BuiltinData -> B.BuiltinData)
unionValueBuiltinRaw =
  $$( compile
        [||
        \bd1 bd2 ->
          B.mkValue (B.unionValue (B.unsafeDataAsValue bd1) (B.unsafeDataAsValue bd2))
        ||]
    )

-- --------------------------------------------------------------------------
-- Raw sorted-merge column. Plinth translation of Philip's pvalueUnionFast.
--
-- Two specialised sorted-merge functions: one for the inner token map (with
-- integer-summing combine), one for the outer currency map (with recursive
-- inner-merge combine). Neither is a higher-order function -- a runtime
-- combinator argument would prevent the plugin from specialising the merge
-- step.
-- --------------------------------------------------------------------------

{-| Inner-level sorted-merge over @BuiltinList (BuiltinPair BuiltinData
BuiltinData)@. Keys are token-name 'ByteString's; values are 'Integer'
quantities. Assumes inputs are sorted by key and quantities are strictly
positive (the sum of two positive integers is never zero, so no zero-strip
pass is needed). -}
mergeInnerSorted
  :: BuiltinList (BuiltinPair BuiltinData BuiltinData)
  -> BuiltinList (BuiltinPair BuiltinData BuiltinData)
  -> BuiltinList (BuiltinPair BuiltinData BuiltinData)
mergeInnerSorted = go
  where
    go lA lB =
      B.caseList'
        lB
        ( \hdA tlA ->
            B.caseList'
              lA
              ( \hdB tlB ->
                  let keyA = BI.unsafeDataAsB (BI.fst hdA)
                      keyB = BI.unsafeDataAsB (BI.fst hdB)
                   in if B.equalsByteString keyA keyB
                        then
                          let qA = BI.unsafeDataAsI (BI.snd hdA)
                              qB = BI.unsafeDataAsI (BI.snd hdB)
                           in BI.mkCons
                                (BI.mkPairData (BI.fst hdA) (BI.mkI (qA + qB)))
                                (go tlA tlB)
                        else
                          if B.lessThanByteString keyA keyB
                            then BI.mkCons hdA (go tlA lB)
                            else BI.mkCons hdB (go lA tlB)
              )
              lB
        )
        lA
{-# INLINEABLE mergeInnerSorted #-}

{-| Outer-level sorted-merge over @BuiltinList (BuiltinPair BuiltinData
BuiltinData)@. Keys are currency-symbol 'ByteString's; values are the
raw inner-map 'BuiltinData'. For a shared currency symbol, the inner
maps are merged with 'mergeInnerSorted' and the combined inner is
wrapped back via 'BI.mkMap'. -}
mergeOuterSorted
  :: BuiltinList (BuiltinPair BuiltinData BuiltinData)
  -> BuiltinList (BuiltinPair BuiltinData BuiltinData)
  -> BuiltinList (BuiltinPair BuiltinData BuiltinData)
mergeOuterSorted = go
  where
    go lA lB =
      B.caseList'
        lB
        ( \hdA tlA ->
            B.caseList'
              lA
              ( \hdB tlB ->
                  let keyA = BI.unsafeDataAsB (BI.fst hdA)
                      keyB = BI.unsafeDataAsB (BI.fst hdB)
                   in if B.equalsByteString keyA keyB
                        then
                          let innerA = BI.unsafeDataAsMap (BI.snd hdA)
                              innerB = BI.unsafeDataAsMap (BI.snd hdB)
                              merged = mergeInnerSorted innerA innerB
                           in BI.mkCons
                                (BI.mkPairData (BI.fst hdA) (BI.mkMap merged))
                                (go tlA tlB)
                        else
                          if B.lessThanByteString keyA keyB
                            then BI.mkCons hdA (go tlA lB)
                            else BI.mkCons hdB (go lA tlB)
              )
              lB
        )
        lA
{-# INLINEABLE mergeOuterSorted #-}

unionValuePositiveRaw :: CompiledCode (B.BuiltinData -> B.BuiltinData -> B.BuiltinData)
unionValuePositiveRaw =
  $$( compile
        [||
        \bd1 bd2 ->
          BI.mkMap
            ( mergeOuterSorted
                (BI.unsafeDataAsMap bd1)
                (BI.unsafeDataAsMap bd2)
            )
        ||]
    )
