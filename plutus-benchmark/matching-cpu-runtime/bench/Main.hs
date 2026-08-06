{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}

-- | One-case-per-process Criterion runner for nested/shallow Match comparison.
module Main (main) where

import Control.DeepSeq (force)
import Control.Exception (evaluate)
import Control.Monad (unless)
import Criterion.Main (bench, defaultMain, env, whnf)
import Data.ByteString.Short qualified as SBS
import Data.List (intercalate)
import Data.SatInt (fromSatInt)
import MatchingCpuRuntime.Arguments qualified as Arguments
import MatchingCpuRuntime.Matchers qualified as Matchers
import PlutusBenchmark.ProtocolParameters qualified as Protocol
import PlutusCore qualified as PLC
import PlutusCore.Evaluation.Machine.ExBudget (ExBudget (..))
import PlutusCore.Evaluation.Machine.ExBudgetingDefaults
  ( defaultCekParametersForTesting
  )
import PlutusCore.Evaluation.Machine.ExMemory (ExCPU (..), ExMemory (..))
import PlutusCore.Version qualified as PLCVersion
import PlutusLedgerApi.Common qualified as Ledger
import System.Environment (getArgs, withArgs)
import UntypedPlutusCore qualified as UPLC
import UntypedPlutusCore.Evaluation.Machine.Cek qualified as Cek

type Term = Arguments.Term

main :: IO ()
main = do
  getArgs >>= \case
    ["--list-cases"] -> mapM_ putStrLn caseNames
    ["--validate-case", requested] ->
      withSelectedCase requested validateSelectedCase
    "--case" : requested : criterionArguments ->
      withArgs criterionArguments $
        withSelectedCase requested benchmarkSelectedCase
    _ ->
      ioError . userError $
        "usage: matching-cpu-runtime --list-cases | "
          <> "--validate-case CASE | --case CASE [CRITERION OPTIONS]"

{-| Direct selection is intentional: it keeps every non-selected top-level Term as an unforced
CAF. The executable must be invoked once per case so the selected CAFs disappear at process exit. -}
withSelectedCase
  :: String
  -> (String -> Int -> Int -> Int -> Integer -> Term -> Term -> IO a)
  -> IO a
withSelectedCase requested run = case requested of
  "constr_flat_d1_w1_c1" ->
    run
      requested
      1
      1
      1
      1
      Matchers.match_benchmark_constr_flat_d1_w1_c1_shallow
      Arguments.match_benchmark_constr_flat_d1_w1_c1_arg
  "constr_flat_d1_w16_c4" ->
    run
      requested
      1
      16
      4
      34
      Matchers.match_benchmark_constr_flat_d1_w16_c4_shallow
      Arguments.match_benchmark_constr_flat_d1_w16_c4_arg
  "constr_flat_d1_w1000_c1" ->
    run
      requested
      1
      1000
      1
      997
      Matchers.match_benchmark_constr_flat_d1_w1000_c1_shallow
      Arguments.match_benchmark_constr_flat_d1_w1000_c1_arg
  "constr_flat_d1_w1000_c16" ->
    run
      requested
      1
      1000
      16
      8452
      Matchers.match_benchmark_constr_flat_d1_w1000_c16_shallow
      Arguments.match_benchmark_constr_flat_d1_w1000_c16_arg
  "constr_spine_front_d4_w16_c8" ->
    run
      requested
      4
      16
      8
      266
      Matchers.match_benchmark_constr_spine_front_d4_w16_c8_shallow
      Arguments.match_benchmark_constr_spine_front_d4_w16_c8_arg
  "constr_spine_middle_d4_w16_c8" ->
    run
      requested
      4
      16
      8
      266
      Matchers.match_benchmark_constr_spine_middle_d4_w16_c8_shallow
      Arguments.match_benchmark_constr_spine_middle_d4_w16_c8_arg
  "constr_spine_last_d4_w16_c8" ->
    run
      requested
      4
      16
      8
      266
      Matchers.match_benchmark_constr_spine_last_d4_w16_c8_shallow
      Arguments.match_benchmark_constr_spine_last_d4_w16_c8_arg
  "constr_spine_irregular_d4_w16_c8" ->
    run
      requested
      4
      16
      8
      266
      Matchers.match_benchmark_constr_spine_irregular_d4_w16_c8_shallow
      Arguments.match_benchmark_constr_spine_irregular_d4_w16_c8_arg
  "constr_spine_irregular_d8_w8_c8" ->
    run
      requested
      8
      8
      8
      257
      Matchers.match_benchmark_constr_spine_irregular_d8_w8_c8_shallow
      Arguments.match_benchmark_constr_spine_irregular_d8_w8_c8_arg
  "constr_spine_front_d64_w2_c8" ->
    run
      requested
      64
      2
      8
      520
      Matchers.match_benchmark_constr_spine_front_d64_w2_c8_shallow
      Arguments.match_benchmark_constr_spine_front_d64_w2_c8_arg
  "constr_spine_zigzag_d100_w2_c10" ->
    run
      requested
      100
      2
      10
      1005
      Matchers.match_benchmark_constr_spine_zigzag_d100_w2_c10_shallow
      Arguments.match_benchmark_constr_spine_zigzag_d100_w2_c10_arg
  "constr_binary_d3_w16_c8" ->
    run
      requested
      3
      16
      8
      504
      Matchers.match_benchmark_constr_binary_d3_w16_c8_shallow
      Arguments.match_benchmark_constr_binary_d3_w16_c8_arg
  "constr_ternary_d3_w8_c10" ->
    run
      requested
      3
      8
      10
      556
      Matchers.match_benchmark_constr_ternary_d3_w8_c10_shallow
      Arguments.match_benchmark_constr_ternary_d3_w8_c10_arg
  "constr_quaternary_d3_w8_c17" ->
    run
      requested
      3
      8
      17
      1485
      Matchers.match_benchmark_constr_quaternary_d3_w8_c17_shallow
      Arguments.match_benchmark_constr_quaternary_d3_w8_c17_arg
  "constr_rootfork2_d6_w12_c8" ->
    run
      requested
      6
      12
      8
      389
      Matchers.match_benchmark_constr_rootfork2_d6_w12_c8_shallow
      Arguments.match_benchmark_constr_rootfork2_d6_w12_c8_arg
  "constr_rootfork3_d5_w10_c9" ->
    run
      requested
      5
      10
      9
      469
      Matchers.match_benchmark_constr_rootfork3_d5_w10_c9_shallow
      Arguments.match_benchmark_constr_rootfork3_d5_w10_c9_arg
  "constr_rootfork4_d4_w8_c8" ->
    run
      requested
      4
      8
      8
      261
      Matchers.match_benchmark_constr_rootfork4_d4_w8_c8_shallow
      Arguments.match_benchmark_constr_rootfork4_d4_w8_c8_arg
  "constr_spine_stress_d10_w100_c20" ->
    run
      requested
      10
      100
      20
      10000
      Matchers.match_benchmark_constr_spine_stress_d10_w100_c20_shallow
      Arguments.match_benchmark_constr_spine_stress_d10_w100_c20_arg
  "constr_binary_stress_d8_w8_c32" ->
    run
      requested
      8
      8
      32
      33024
      Matchers.match_benchmark_constr_binary_stress_d8_w8_c32_shallow
      Arguments.match_benchmark_constr_binary_stress_d8_w8_c32_arg
  "constr_alt_spine_d16_w8_c8" ->
    run
      requested
      16
      8
      8
      544
      Matchers.match_benchmark_constr_alt_spine_d16_w8_c8_shallow
      Arguments.match_benchmark_constr_alt_spine_d16_w8_c8_arg
  "constr_alt_rootfork3_d5_w10_c9" ->
    run
      requested
      5
      10
      9
      469
      Matchers.match_benchmark_constr_alt_rootfork3_d5_w10_c9_shallow
      Arguments.match_benchmark_constr_alt_rootfork3_d5_w10_c9_arg
  "constr_alt_binary_d8_w8_c32" ->
    run
      requested
      8
      8
      32
      33024
      Matchers.match_benchmark_constr_alt_binary_d8_w8_c32_shallow
      Arguments.match_benchmark_constr_alt_binary_d8_w8_c32_arg
  _ -> ioError . userError $ "unknown benchmark case: " <> requested

benchmarkSelectedCase
  :: String -> Int -> Int -> Int -> Integer -> Term -> Term -> IO ()
benchmarkSelectedCase caseId _depth _width _captures expected matcher argument =
  defaultMain
    [ env (prepareCase expected matcher argument) $ \ ~applied ->
        bench (Matchers.matching_implementation <> "/" <> caseId) $
          whnf runCEK applied
    ]

prepareCase :: Integer -> Term -> Term -> IO Term
prepareCase expected matcher argument = do
  applied <- evaluate . force $ UPLC.applyTerm matcher argument
  actual <- evaluate $ runCEK applied
  unless (actual == expected) . errorWithoutStackTrace $
    "correctness check failed: expected " <> show expected <> ", got " <> show actual
  pure applied

runCEK :: Term -> Integer
runCEK =
  extractInteger
    . Cek._cekReportResult
    . Cek.runCekDeBruijn
      defaultCekParametersForTesting
      Cek.restrictingEnormous
      Cek.noEmitter

extractInteger
  :: Cek.CekResult PLC.NamedDeBruijn PLC.DefaultUni PLC.DefaultFun
  -> Integer
extractInteger = \case
  Cek.CekSuccessConstant (PLC.Some (PLC.ValueOf PLC.DefaultUniInteger result)) -> result
  failure@(Cek.CekFailure _) -> case Cek.cekResultToEither failure of
    Left err -> errorWithoutStackTrace $ "CEK evaluation failed: " <> show err
    Right _ -> errorWithoutStackTrace "impossible successful conversion of CEK failure"
  Cek.CekSuccessConstant _ ->
    errorWithoutStackTrace "CEK returned a non-integer constant"
  Cek.CekSuccessNonConstant _ ->
    errorWithoutStackTrace "CEK returned a non-constant term"

validateSelectedCase
  :: String -> Int -> Int -> Int -> Integer -> Term -> Term -> IO ()
validateSelectedCase caseId depth width captures expected matcher argument = do
  applied <- prepareCase expected matcher argument
  let report =
        Cek.runCekDeBruijn
          defaultCekParametersForTesting
          Cek.counting
          Cek.noEmitter
          applied
      actual = extractInteger $ Cek._cekReportResult report
      Cek.CountingSt budget = Cek._cekReportCost report
      (cpu, memory) = budgetParts budget
      bytes = scriptBytes matcher
      sizeOk = toInteger bytes <= Protocol.max_tx_size
      cpuOk = cpu <= Protocol.max_tx_ex_steps
      memoryOk = memory <= Protocol.max_tx_ex_mem
  _ <- evaluate actual
  putStrLn
    "implementation,case_id,depth,width,captures,expected,actual,script_bytes,cpu,memory,size_ok,cpu_ok,memory_ok"
  putStrLn . intercalate "," $
    [ Matchers.matching_implementation
    , caseId
    , show depth
    , show width
    , show captures
    , show expected
    , show actual
    , show bytes
    , show cpu
    , show memory
    , show sizeOk
    , show cpuOk
    , show memoryOk
    ]
  unless (sizeOk && cpuOk && memoryOk) . errorWithoutStackTrace $
    "case exceeds a protocol limit: " <> caseId

scriptBytes :: Term -> Int
scriptBytes matcher =
  SBS.length . Ledger.serialiseUPLC $
    UPLC.Program () PLCVersion.plcVersion120 $
      UPLC.termMapNames UPLC.unNameDeBruijn matcher

budgetParts :: ExBudget -> (Integer, Integer)
budgetParts (ExBudget (ExCPU cpu) (ExMemory memory)) =
  (fromSatInt cpu, fromSatInt memory)

caseNames :: [String]
caseNames =
  [ "constr_flat_d1_w1_c1"
  , "constr_flat_d1_w16_c4"
  , "constr_flat_d1_w1000_c1"
  , "constr_flat_d1_w1000_c16"
  , "constr_spine_front_d4_w16_c8"
  , "constr_spine_middle_d4_w16_c8"
  , "constr_spine_last_d4_w16_c8"
  , "constr_spine_irregular_d4_w16_c8"
  , "constr_spine_irregular_d8_w8_c8"
  , "constr_spine_front_d64_w2_c8"
  , "constr_spine_zigzag_d100_w2_c10"
  , "constr_binary_d3_w16_c8"
  , "constr_ternary_d3_w8_c10"
  , "constr_quaternary_d3_w8_c17"
  , "constr_rootfork2_d6_w12_c8"
  , "constr_rootfork3_d5_w10_c9"
  , "constr_rootfork4_d4_w8_c8"
  , "constr_spine_stress_d10_w100_c20"
  , "constr_binary_stress_d8_w8_c32"
  , "constr_alt_spine_d16_w8_c8"
  , "constr_alt_rootfork3_d5_w10_c9"
  , "constr_alt_binary_d8_w8_c32"
  ]
