-- editorconfig-checker-disable-file
{-# LANGUAGE OverloadedStrings #-}

{-| Tests that different CEK machine evaluation paths produce identical ExBudget
for the same term. This addresses the concern from
https://github.com/IntersectMBO/plutus-private/issues/2084 that using
'runCekNoEmit' with 'defaultCekParametersForVariant' might produce different
budget numbers than using 'evaluateTerm' with a properly constructed
'EvaluationContext'.

We compare three paths:

  Path A ("direct"): 'defaultCekParametersForVariant' — uses noinline, reads the
  cost model from JSON directly, no applyCostModelParams round-trip.

  Path B ("benchmark"): 'defaultCostModelParamsForVariant' fed to
  'mkDynEvaluationContext' — uses inline, goes through
  applyCostModelParams (JSON round-trip).

  Path C ("production"): V3.'mkEvaluationContext' with @[Int64]@ in ledger
  order — the exact code path the node uses.

Note: Path A uses @def :: CaserBuiltin@ while Paths B/C use a proper CaserBuiltin.
The test terms avoid 'Case' on built-in types, so this difference does not
affect the budget. -}
module Spec.BudgetConsistency (tests) where

import PlutusCore.Builtin (CaserBuiltin (..), caseBuiltin)
import PlutusCore.Data (Data (..))
import PlutusCore.Default
import PlutusCore.Evaluation.Machine.CostModelInterface (CostModelParams)
import PlutusCore.Evaluation.Machine.ExBudget (ExBudget (..))
import PlutusCore.Evaluation.Machine.ExBudgetingDefaults qualified as PLC
import PlutusCore.MkPlc (mkConstant)
import PlutusLedgerApi.Common
  ( EvaluationContext
  , MajorProtocolVersion
  , PlutusLedgerLanguage (..)
  , mkDynEvaluationContext
  , toCostModelParams
  , toMachineParameters
  )
import PlutusLedgerApi.Common.Versions (changPV)
import PlutusLedgerApi.Test.V2.EvaluationContext qualified as V2Test
import PlutusLedgerApi.Test.V3.EvaluationContext qualified as V3Test
import PlutusLedgerApi.V2.EvaluationContext qualified as V2
import PlutusLedgerApi.V3.EvaluationContext qualified as V3
import PlutusPrelude (unsafeFromRight)
import UntypedPlutusCore qualified as UPLC
import UntypedPlutusCore.Evaluation.Machine.Cek qualified as Cek

import Control.Monad (when)
import Control.Monad.Writer (runWriterT)
import Data.ByteString (ByteString)
import Data.List (foldl')
import Data.Map.Strict qualified as Map
import Data.Maybe (fromJust)
import Data.Text (Text)
import Test.Tasty
import Test.Tasty.HUnit

-- | Type alias for the terms we test with.
type NTerm = UPLC.Term UPLC.NamedDeBruijn DefaultUni DefaultFun ()

-- -------------------------------------------------------------------
-- VariantC configuration
-- -------------------------------------------------------------------

-- | Semantics variant under test: VariantC corresponds to Chang era (PV9).
semVarC :: BuiltinSemanticsVariant DefaultFun
semVarC = DefaultFunSemanticsVariantC

-- | Protocol version that maps to VariantC for PlutusV3.
pvC :: MajorProtocolVersion
pvC = changPV

-- -------------------------------------------------------------------
-- VariantB configuration
-- -------------------------------------------------------------------

-- | Semantics variant under test: VariantB corresponds to Chang era (PV9) for PlutusV2.
semVarB :: BuiltinSemanticsVariant DefaultFun
semVarB = DefaultFunSemanticsVariantB

-- | Protocol version that maps to VariantB for PlutusV2.
pvB :: MajorProtocolVersion
pvB = changPV

-- -------------------------------------------------------------------
-- Kitchen sink term
-- -------------------------------------------------------------------

{-| A single term exercising 55 builtins available at changPV (PV9,
batch 1–4). Each builtin is called with minimal valid arguments; results
are chained via 'seq_' so every call is fully evaluated by the CEK machine.

Builtins NOT covered (need complex test data or are in later batches):
  - VerifyEd25519Signature, VerifyEcdsaSecp256k1Signature,
    VerifySchnorrSecp256k1Signature (need valid signatures)
  - BLS12_381_* (17 builtins, need group elements)
  - Batch 5 bitwise ops (plominPV), Batch 6 (vanRossemPV) -}
termKitchenSink :: NTerm
termKitchenSink = foldr seq_ unit_ expressions
  where
    expressions =
      -- Integer arithmetic (10)
      [ ap (blt AddInteger) [int_ 99, int_ 2]
      , ap (blt SubtractInteger) [int_ 88, int_ 3]
      , ap (blt MultiplyInteger) [int_ 7, int_ 8]
      , ap (blt DivideInteger) [int_ 100, int_ 3]
      , ap (blt QuotientInteger) [int_ 100, int_ 3]
      , ap (blt RemainderInteger) [int_ 100, int_ 3]
      , ap (blt ModInteger) [int_ 100, int_ 3]
      , ap (blt EqualsInteger) [int_ 42, int_ 42]
      , ap (blt LessThanInteger) [int_ 1, int_ 2]
      , ap (blt LessThanEqualsInteger) [int_ 1, int_ 2]
      , -- ByteString operations (8)
        ap (blt AppendByteString) [bs_ "abc", bs_ "def"]
      , ap (blt ConsByteString) [int_ 65, bs_ "bc"]
      , ap (blt SliceByteString) [int_ 0, int_ 2, bs_ "hello"]
      , ap (blt LengthOfByteString) [bs_ "hello"]
      , ap (blt IndexByteString) [bs_ "hello", int_ 0]
      , ap (blt EqualsByteString) [bs_ "abc", bs_ "abc"]
      , ap (blt LessThanByteString) [bs_ "abc", bs_ "abd"]
      , ap (blt LessThanEqualsByteString) [bs_ "abc", bs_ "abd"]
      , -- Crypto hashes (5)
        ap (blt Sha2_256) [bs_ "test"]
      , ap (blt Sha3_256) [bs_ "test"]
      , ap (blt Blake2b_256) [bs_ "test"]
      , ap (blt Keccak_256) [bs_ "test"]
      , ap (blt Blake2b_224) [bs_ "test"]
      , -- String operations (4)
        ap (blt AppendString) [str_ "hello", str_ " world"]
      , ap (blt EqualsString) [str_ "abc", str_ "abc"]
      , ap (blt EncodeUtf8) [str_ "hello"]
      , ap (blt DecodeUtf8) [bs_ "hello"]
      , -- Data constructors and destructors (15)
        ap (blt IData) [int_ 42]
      , ap (blt BData) [bs_ "test"]
      , ap (blt UnIData) [dat_ (I 42)]
      , ap (blt UnBData) [dat_ (B "test")]
      , ap (blt ConstrData) [int_ 0, datList_ [I 1, I 2]]
      , ap (blt ListData) [datList_ [I 1, I 2]]
      , ap (blt MapData) [pairList_ [(I 1, B "x")]]
      , ap (blt UnConstrData) [dat_ (Constr 0 [I 1])]
      , ap (blt UnMapData) [dat_ (Map [(I 1, B "x")])]
      , ap (blt UnListData) [dat_ (List [I 1])]
      , ap (blt EqualsData) [dat_ (I 1), dat_ (I 1)]
      , ap (blt SerialiseData) [dat_ (I 42)]
      , ap (blt MkPairData) [dat_ (I 1), dat_ (B "x")]
      , ap (blt MkNilData) [unit_]
      , ap (blt MkNilPairData) [unit_]
      , -- Conversion (2)
        ap (blt IntegerToByteString) [bool_ True, int_ 4, int_ 42]
      , ap (blt ByteStringToInteger) [bool_ True, bs_ "\x00\x2a"]
      , -- 1 Force: polymorphic builtins (8)
        ap (force (blt IfThenElse)) [bool_ True, int_ 1, int_ 2]
      , ap (force (blt HeadList)) [datList_ [I 1, I 2]]
      , ap (force (blt TailList)) [datList_ [I 1, I 2]]
      , ap (force (blt NullList)) [datList_ []]
      , ap (force (blt MkCons)) [dat_ (I 1), datList_ []]
      , ap (force (blt Trace)) [str_ "x", int_ 1]
      , ap (force (blt ChooseUnit)) [unit_, int_ 1]
      , ap
          (force (blt ChooseData))
          [dat_ (I 42), int_ 1, int_ 2, int_ 3, int_ 4, int_ 5]
      , -- 2 Forces: polymorphic builtins (3)
        ap (forceN 2 (blt FstPair)) [datPair_ (I 1, B "x")]
      , ap (forceN 2 (blt SndPair)) [datPair_ (I 1, B "x")]
      , ap (forceN 2 (blt ChooseList)) [datList_ [], int_ 1, int_ 2]
      ]

-- -------------------------------------------------------------------
-- Evaluation paths (VariantC / V3)
-- -------------------------------------------------------------------

-- | Extract ExBudget from a counting-mode CekReport.
extractBudget
  :: Cek.CekReport Cek.CountingSt UPLC.NamedDeBruijn DefaultUni DefaultFun -> ExBudget
extractBudget (Cek.CekReport _result (Cek.CountingSt budget) _logs) = budget

{-| Path A: Direct CEK via 'defaultCekParametersForVariant'.
This is how the bug report (issue 2084) and some tests run scripts.
Uses noinline, no JSON round-trip of cost model params. -}
budgetDirect :: NTerm -> ExBudget
budgetDirect =
  extractBudget
    . Cek.runCekDeBruijn
      (PLC.defaultCekParametersForVariant semVarC)
      Cek.counting
      Cek.noEmitter

{-| Path B: Via 'mkDynEvaluationContext' + 'defaultCostModelParamsForVariant'.
This is how validation benchmarks build EvaluationContext (mkEvalCtx).
Uses inline, JSON round-trip via applyCostModelParams. -}
benchmarkEvalCtx :: EvaluationContext
benchmarkEvalCtx =
  case PLC.defaultCostModelParamsForVariant semVarC of
    Just p ->
      either (error . show) id $
        mkDynEvaluationContext
          PlutusV3
          (\_ -> CaserBuiltin caseBuiltin)
          [semVarC]
          (const semVarC)
          p
    Nothing -> error "defaultCostModelParamsForVariant: Nothing"

budgetBenchmark :: NTerm -> ExBudget
budgetBenchmark =
  extractBudget
    . Cek.runCekDeBruijn
      (toMachineParameters pvC benchmarkEvalCtx)
      Cek.counting
      Cek.noEmitter

{-| Path C: Via V3.'mkEvaluationContext' + @[Int64]@ in ledger order.
This is how the Cardano node builds EvaluationContext. -}
productionEvalCtx :: EvaluationContext
productionEvalCtx =
  fst . unsafeFromRight . runWriterT $
    V3.mkEvaluationContext (map snd V3Test.costModelParamsForTesting)

budgetProduction :: NTerm -> ExBudget
budgetProduction =
  extractBudget
    . Cek.runCekDeBruijn
      (toMachineParameters pvC productionEvalCtx)
      Cek.counting
      Cek.noEmitter

-- -------------------------------------------------------------------
-- Evaluation paths (VariantB / V2)
-- -------------------------------------------------------------------

{-| Path C for VariantB: Via V2.'mkEvaluationContext' + @[Int64]@ in ledger order.
This is how the Cardano node builds the V2 EvaluationContext. -}
productionEvalCtxB :: EvaluationContext
productionEvalCtxB =
  fst . unsafeFromRight . runWriterT $
    V2.mkEvaluationContext (map snd V2Test.costModelParamsForTesting)

budgetProductionB :: NTerm -> ExBudget
budgetProductionB =
  extractBudget
    . Cek.runCekDeBruijn
      (toMachineParameters pvB productionEvalCtxB)
      Cek.counting
      Cek.noEmitter

budgetDirectB :: NTerm -> ExBudget
budgetDirectB =
  extractBudget
    . Cek.runCekDeBruijn
      (PLC.defaultCekParametersForVariant semVarB)
      Cek.counting
      Cek.noEmitter

-- -------------------------------------------------------------------
-- Cost model params helpers
-- -------------------------------------------------------------------

{-| Print the differences between two 'CostModelParams' maps.
Shows keys only in the first, only in the second, and value mismatches. -}
printParamDifferences :: CostModelParams -> CostModelParams -> IO ()
printParamDifferences paramsAB paramsC = do
  let onlyAB = Map.difference paramsAB paramsC
      onlyC = Map.difference paramsC paramsAB
      differ =
        Map.mapMaybe id $
          Map.intersectionWith
            (\a c -> if a == c then Nothing else Just (a, c))
            paramsAB
            paramsC
  putStrLn ""
  putStrLn $ "  Total keys in A/B: " ++ show (Map.size paramsAB)
  putStrLn $ "  Total keys in C:   " ++ show (Map.size paramsC)
  when (not $ null onlyAB) $ do
    putStrLn $ "  Keys only in A/B (" ++ show (Map.size onlyAB) ++ "):"
    mapM_
      (\(k, v) -> putStrLn $ "    " ++ show k ++ " = " ++ show v)
      (Map.toList onlyAB)
  when (not $ null onlyC) $ do
    putStrLn $ "  Keys only in C (" ++ show (Map.size onlyC) ++ "):"
    mapM_
      (\(k, v) -> putStrLn $ "    " ++ show k ++ " = " ++ show v)
      (Map.toList onlyC)
  when (not $ null differ) $ do
    putStrLn $ "  Value mismatches (" ++ show (Map.size differ) ++ "):"
    mapM_
      (\(k, (a, c)) -> putStrLn $ "    " ++ show k ++ ": A/B=" ++ show a ++ " C=" ++ show c)
      (Map.toList differ)
  when (null onlyAB && null onlyC && null differ) $
    putStrLn "  Params are identical."

-- -------------------------------------------------------------------
-- Tests
-- -------------------------------------------------------------------

tests :: TestTree
tests =
  testGroup
    "Budget consistency across evaluation paths"
    [ variantCTests
    , variantBTests
    ]

{-| VariantC (V3, changPV) budget and cost model param tests.
Exercises all three evaluation paths and compares ExBudgets and CostModelParams. -}
variantCTests :: TestTree
variantCTests =
  testGroup
    "VariantC (changPV, V3)"
    [ testCase "direct (A) == benchmark (B)" $
        budgetDirect termKitchenSink @?= budgetBenchmark termKitchenSink
    , testCase "benchmark (B) == production (C)" $
        budgetBenchmark termKitchenSink @?= budgetProduction termKitchenSink
    , testCase "direct (A) == production (C)" $
        budgetDirect termKitchenSink @?= budgetProduction termKitchenSink
    , testCase "budgets are non-zero" $ do
        let b = budgetDirect termKitchenSink
        assertBool "CPU should be positive" (exBudgetCPU b > 0)
        assertBool "Memory should be positive" (exBudgetMemory b > 0)
    , testCase "cost model params: A/B == C" $ do
        let paramsAB = fromJust $ PLC.defaultCostModelParamsForVariant semVarC
            paramsC = toCostModelParams V3Test.costModelParamsForTesting
        printParamDifferences paramsAB paramsC
        paramsAB @?= paramsC
    , testCase "print all budgets for inspection" $ do
        putStrLn ""
        putStrLn $ "  Path A (direct):     " ++ show (budgetDirect termKitchenSink)
        putStrLn $ "  Path B (benchmark):  " ++ show (budgetBenchmark termKitchenSink)
        putStrLn $ "  Path C (production): " ++ show (budgetProduction termKitchenSink)
    ]

{-| VariantB (V2, changPV) cost model param and budget tests.
This is the variant Ana identified as potentially having different cost models
between 'defaultCekParametersForVariant' and 'mkEvaluationContext'. -}
variantBTests :: TestTree
variantBTests =
  testGroup
    "VariantB (changPV, V2)"
    [ testCase "cost model params: A/B vs C (diagnostic)" $ do
        let paramsAB = fromJust $ PLC.defaultCostModelParamsForVariant semVarB
            paramsC = toCostModelParams V2Test.costModelParamsForTesting
        printParamDifferences paramsAB paramsC
        -- This may fail: Path C for V2 clears V3-only builtins,
        -- so it will have fewer keys than Path A/B.
        paramsAB @?= paramsC
    , testCase "budget: direct (A) vs production (C)" $ do
        let bA = budgetDirectB termKitchenSinkV2
            bC = budgetProductionB termKitchenSinkV2
        putStrLn ""
        putStrLn $ "  Path A (direct):     " ++ show bA
        putStrLn $ "  Path C (production): " ++ show bC
        bA @?= bC
    ]

-- -------------------------------------------------------------------
-- Kitchen sink term for V2 (only V2-available builtins)
-- -------------------------------------------------------------------

{-| A term exercising builtins available at changPV for PlutusV2.
Excludes V3-only builtins (BLS, Keccak_256, Blake2b_224,
IntegerToByteString, ByteStringToInteger, bitwise ops, etc.). -}
termKitchenSinkV2 :: NTerm
termKitchenSinkV2 = foldr seq_ unit_ expressions
  where
    expressions =
      -- Integer arithmetic (10)
      [ ap (blt AddInteger) [int_ 99, int_ 2]
      , ap (blt SubtractInteger) [int_ 88, int_ 3]
      , ap (blt MultiplyInteger) [int_ 7, int_ 8]
      , ap (blt DivideInteger) [int_ 100, int_ 3]
      , ap (blt QuotientInteger) [int_ 100, int_ 3]
      , ap (blt RemainderInteger) [int_ 100, int_ 3]
      , ap (blt ModInteger) [int_ 100, int_ 3]
      , ap (blt EqualsInteger) [int_ 42, int_ 42]
      , ap (blt LessThanInteger) [int_ 1, int_ 2]
      , ap (blt LessThanEqualsInteger) [int_ 1, int_ 2]
      , -- ByteString operations (8)
        ap (blt AppendByteString) [bs_ "abc", bs_ "def"]
      , ap (blt ConsByteString) [int_ 65, bs_ "bc"]
      , ap (blt SliceByteString) [int_ 0, int_ 2, bs_ "hello"]
      , ap (blt LengthOfByteString) [bs_ "hello"]
      , ap (blt IndexByteString) [bs_ "hello", int_ 0]
      , ap (blt EqualsByteString) [bs_ "abc", bs_ "abc"]
      , ap (blt LessThanByteString) [bs_ "abc", bs_ "abd"]
      , ap (blt LessThanEqualsByteString) [bs_ "abc", bs_ "abd"]
      , -- Crypto hashes (3 — V2 only has Sha2, Sha3, Blake2b_256)
        ap (blt Sha2_256) [bs_ "test"]
      , ap (blt Sha3_256) [bs_ "test"]
      , ap (blt Blake2b_256) [bs_ "test"]
      , -- String operations (4)
        ap (blt AppendString) [str_ "hello", str_ " world"]
      , ap (blt EqualsString) [str_ "abc", str_ "abc"]
      , ap (blt EncodeUtf8) [str_ "hello"]
      , ap (blt DecodeUtf8) [bs_ "hello"]
      , -- Data constructors and destructors (13 — V2 has SerialiseData)
        ap (blt IData) [int_ 42]
      , ap (blt BData) [bs_ "test"]
      , ap (blt UnIData) [dat_ (I 42)]
      , ap (blt UnBData) [dat_ (B "test")]
      , ap (blt ConstrData) [int_ 0, datList_ [I 1, I 2]]
      , ap (blt ListData) [datList_ [I 1, I 2]]
      , ap (blt MapData) [pairList_ [(I 1, B "x")]]
      , ap (blt UnConstrData) [dat_ (Constr 0 [I 1])]
      , ap (blt UnMapData) [dat_ (Map [(I 1, B "x")])]
      , ap (blt UnListData) [dat_ (List [I 1])]
      , ap (blt EqualsData) [dat_ (I 1), dat_ (I 1)]
      , ap (blt SerialiseData) [dat_ (I 42)]
      , ap (blt MkPairData) [dat_ (I 1), dat_ (B "x")]
      , ap (blt MkNilData) [unit_]
      , ap (blt MkNilPairData) [unit_]
      , -- 1 Force: polymorphic builtins (8)
        ap (force (blt IfThenElse)) [bool_ True, int_ 1, int_ 2]
      , ap (force (blt HeadList)) [datList_ [I 1, I 2]]
      , ap (force (blt TailList)) [datList_ [I 1, I 2]]
      , ap (force (blt NullList)) [datList_ []]
      , ap (force (blt MkCons)) [dat_ (I 1), datList_ []]
      , ap (force (blt Trace)) [str_ "x", int_ 1]
      , ap (force (blt ChooseUnit)) [unit_, int_ 1]
      , ap
          (force (blt ChooseData))
          [dat_ (I 42), int_ 1, int_ 2, int_ 3, int_ 4, int_ 5]
      , -- 2 Forces: polymorphic builtins (3)
        ap (forceN 2 (blt FstPair)) [datPair_ (I 1, B "x")]
      , ap (forceN 2 (blt SndPair)) [datPair_ (I 1, B "x")]
      , ap (forceN 2 (blt ChooseList)) [datList_ [], int_ 1, int_ 2]
      ]

-- -------------------------------------------------------------------
-- UPLC smart constructors
-- -------------------------------------------------------------------

app :: NTerm -> NTerm -> NTerm
app = UPLC.Apply ()

-- | Iterated application: @ap f [a, b, c] = f a b c@.
ap :: NTerm -> [NTerm] -> NTerm
ap = foldl' app

force :: NTerm -> NTerm
force = UPLC.Force ()

-- | Force @n@ times (for polymorphic builtins with multiple type variables).
forceN :: Int -> NTerm -> NTerm
forceN n t = iterate force t !! n

blt :: DefaultFun -> NTerm
blt = UPLC.Builtin ()

-- | Lambda abstraction (unused binder for sequencing).
lam :: NTerm -> NTerm
lam = UPLC.LamAbs () (UPLC.NamedDeBruijn "_" 0)

-- | Evaluate @a@, discard its result, return @b@.
seq_ :: NTerm -> NTerm -> NTerm
seq_ a b = app (lam b) a

-- Constants
int_ :: Integer -> NTerm
int_ = mkConstant ()

bs_ :: ByteString -> NTerm
bs_ = mkConstant ()

str_ :: Text -> NTerm
str_ = mkConstant ()

bool_ :: Bool -> NTerm
bool_ = mkConstant ()

unit_ :: NTerm
unit_ = mkConstant () ()

dat_ :: Data -> NTerm
dat_ = mkConstant ()

datList_ :: [Data] -> NTerm
datList_ = mkConstant ()

datPair_ :: (Data, Data) -> NTerm
datPair_ = mkConstant ()

pairList_ :: [(Data, Data)] -> NTerm
pairList_ = mkConstant ()
