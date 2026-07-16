{-# LANGUAGE BangPatterns #-}

-- | Benchmarks for matching patterns against builtin values.
module Main (main) where

import Criterion.Main

import PlutusBenchmark.Common (Term, getConfig, mkMostRecentEvalCtx)
import PlutusCore.Builtin qualified as PLC
import PlutusCore.Evaluation.Machine.ExBudget (ExBudget (..), ExRestrictingBudget (..))
import PlutusCore.Evaluation.Machine.MachineParameters (MachineParameters (..))
import PlutusLedgerApi.Common (EvaluationContext)
import PlutusLedgerApi.Common qualified as LedgerApi
import UntypedPlutusCore.Evaluation.Machine.Cek qualified as Cek

import PlutusBenchmark.Matching qualified as Matching

import Control.DeepSeq (force)
import Control.Exception
import Data.Functor

benchmarks :: EvaluationContext -> [Benchmark]
benchmarks ctx =
  [ bgroup
      "matching"
      [ mkMatchBMs "wildcard" Matching.matchingWildcard
      , mkMatchBMs "integer" Matching.matchingInteger
      , mkMatchBMs "exact list" Matching.matchingExactList
      , mkMatchBMs "capture list" Matching.matchingCaptureList
      , mkMatchBMs "alternatives" Matching.matchingAlternatives
      , bgroup
          "Data.Constr comparison"
          [ bgroup ("width " <> show width) $
              let (directUnConstr, checkedUnConstr, wildcardMatch, captureMatch) =
                    Matching.dataConstrMatchComparison width
               in [ bench "direct UnConstrData" $ benchTermCekWithMatch ctx directUnConstr
                  , bench "checked ChooseData + UnConstrData" $
                      benchTermCekWithMatch ctx checkedUnConstr
                  , bench "Match wildcards" $ benchTermCekWithMatch ctx wildcardMatch
                  , bench "Match captures" $ benchTermCekWithMatch ctx captureMatch
                  ]
          | width <- [0, 1, 3, 16, 128]
          ]
      , bgroup
          "fixed-point exhaustion"
          [ mkExhaustionBM "exact list/1200" $ Matching.matchingFixpointExactList 1200
          , mkExhaustionBM "late list mismatch/1200" $
              Matching.matchingFixpointLateListMismatch 1200
          , mkExhaustionBM "abandoned captures/700" $
              Matching.matchingFixpointAbandonedCaptures 700
          , mkExhaustionBM "short list arity/1200" $
              Matching.matchingFixpointListArityMismatch 1200 (-1)
          , mkExhaustionBM "long list arity/1200" $
              Matching.matchingFixpointListArityMismatch 1200 1
          , mkExhaustionBM "capture list/700" $ Matching.matchingFixpointCaptureList 700
          , mkExhaustionBM "alternatives/1000" $ Matching.matchingFixpointAlternatives 1000
          , mkExhaustionBM "wide alternatives/16x64" $
              Matching.matchingFixpointWideAlternatives 16 64
          , mkExhaustionBM "nested Data/1000" $ Matching.matchingFixpointNestedData 1000
          , mkExhaustionBM "nested Data.Constr/1000" $
              Matching.matchingFixpointNestedDataConstr 1000
          , mkExhaustionBM "empty Data.Constr" Matching.matchingFixpointEmptyDataConstr
          , mkExhaustionBM "small integer" Matching.matchingFixpointSmallInteger
          , mkExhaustionBM "small bytestring" Matching.matchingFixpointSmallByteString
          , mkExhaustionBM "wide Data.Constr/1200" $
              Matching.matchingFixpointWideDataConstr 1200
          , mkExhaustionBM "max Int64 integer" Matching.matchingFixpointMaxInteger
          , mkExhaustionBM "large bytestring/1000 words" $
              Matching.matchingFixpointLargeByteString 1000
          , mkExhaustionBM "max Word64 Data tag" Matching.matchingFixpointMaxDataTag
          ]
      ]
  ]
  where
    mkMatchBMs name f =
      bgroup name $
        [200, 400 .. 1200] <&> \n ->
          bench (show n) $ benchTermCekWithMatch ctx (f n)
    mkExhaustionBM name term =
      bench name $ benchTermCekWithMatchExhaustion ctx term

{-| Benchmark an experimental 'UPLC.Match' term using the production CEK and the same
machine variant/cost model as 'benchTermCek', but with the 'DefaultUni' matcher enabled
for this invocation only. Ledger evaluation contexts deliberately keep matching disabled
until PLC 1.2 receives a ledger activation. -}
benchTermCekWithMatch :: EvaluationContext -> Term -> Benchmarkable
benchTermCekWithMatch evalCtx term =
  let !term' = force term
   in whnf runMatch term'
  where
    runMatch =
      either (error . show) (const ())
        . Cek.cekResultToEither
        . Cek._cekReportResult
        . Cek.runCekDeBruijn matchParameters Cek.restrictingEnormous Cek.noEmitter
    matchParameters =
      case LedgerApi.toMachineParameters benchmarkProtocolVersion evalCtx of
        MachineParameters caser _matcher variantParameters ->
          MachineParameters caser PLC.availableMatcherBuiltin variantParameters
    -- Keep this aligned with 'PlutusBenchmark.Common.evaluateCekLikeInProd'.
    benchmarkProtocolVersion = LedgerApi.ledgerLanguageIntroducedIn LedgerApi.PlutusV1

{-| Benchmark recursive experimental matches that are expected to consume a ledger-scale budget.
The result is checked specifically for budget exhaustion so a malformed benchmark or unrelated CEK
failure cannot be mistaken for a fast successful run. -}
benchTermCekWithMatchExhaustion :: EvaluationContext -> Term -> Benchmarkable
benchTermCekWithMatchExhaustion evalCtx term =
  let !term' = force term
   in whnf runMatchToExhaustion term'
  where
    runMatchToExhaustion term' =
      case Cek.cekResultToEither . Cek._cekReportResult $
        Cek.runCekDeBruijn
          matchParameters
          (Cek.restricting nearMaximumCpuBudget)
          Cek.noEmitter
          term' of
        Left (Cek.ErrorWithCause (Cek.OperationalError (Cek.CekOutOfExError _)) _) -> ()
        result -> error $ "fixed-point Match did not exhaust its budget: " <> show result
    matchParameters =
      case LedgerApi.toMachineParameters benchmarkProtocolVersion evalCtx of
        MachineParameters caser _matcher variantParameters ->
          MachineParameters caser PLC.availableMatcherBuiltin variantParameters
    -- Keep memory nonbinding to measure the worst latency at the current ledger CPU ceiling.
    nearMaximumCpuBudget = ExRestrictingBudget $ ExBudget 10000000000 1000000000
    benchmarkProtocolVersion = LedgerApi.ledgerLanguageIntroducedIn LedgerApi.PlutusV1

main :: IO ()
main = do
  -- Run each benchmark for at least 15 seconds.  Change this with -L or --timeout.
  config <- getConfig 15.0
  evalCtx <- evaluate mkMostRecentEvalCtx
  defaultMainWith config $ benchmarks evalCtx
