{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeApplications #-}

-- | Benchmarks for matching patterns against builtin values.
module Main (main) where

import Criterion.Main
import Criterion.Types (Config (..))

import PlutusBenchmark.Common (Term, getConfig, mkMostRecentEvalCtx)
import PlutusCore qualified as Core
import PlutusCore.Builtin qualified as PLC
import PlutusCore.Evaluation.Machine.ExBudget (ExBudget (..), ExRestrictingBudget (..))
import PlutusCore.Evaluation.Machine.MachineParameters (MachineParameters (..))
import PlutusLedgerApi.Common (EvaluationContext)
import PlutusLedgerApi.Common qualified as LedgerApi
import UntypedPlutusCore qualified as UPLC
import UntypedPlutusCore.Evaluation.Machine.Cek qualified as Cek

import PlutusBenchmark.Matching qualified as Matching
import PlutusBenchmark.Matching.Comparison qualified as Comparison

import Control.DeepSeq (force)
import Control.Exception
import Control.Monad (forM_, when)
import Data.Functor
import Data.Maybe (isJust)
import System.Environment (lookupEnv)

benchmarks :: Bool -> EvaluationContext -> [Benchmark]
benchmarks reverseVariants ctx =
  [ bgroup
      "matching"
      [ bgroup
          "comparisons"
          [ bgroup (Comparison.comparisonCaseId comparison) $
              [ bench (Comparison.comparisonVariantId variant) $
                  benchTermCekWithMatch ctx (Comparison.comparisonVariantTerm variant)
              | variant <- orderVariants $ Comparison.comparisonVariants comparison
              ]
          | comparison <- Comparison.comparisonCases
          ]
      , bgroup
          "large-target-comparisons"
          [ bgroup (Comparison.comparisonCaseId comparison) $
              [ bench (Comparison.comparisonVariantId variant) $
                  benchTermCekWithMatch ctx (Comparison.comparisonVariantTerm variant)
              | variant <- orderVariants $ Comparison.comparisonVariants comparison
              ]
          | comparison <- Comparison.largeTargetComparisonCases
          ]
      , mkMatchBMs "wildcard" Matching.matchingWildcard
      , mkMatchBMs "integer" Matching.matchingInteger
      , mkMatchBMs "exact list" Matching.matchingExactList
      , mkMatchBMs "capture list" Matching.matchingCaptureList
      , bgroup
          "list prefix"
          [ bgroup ("prefix " <> show prefixWidth) $
              [ bgroup
                  "wildcard rest"
                  [ bench ("suffix " <> show suffixWidth) $
                      benchTermCekWithMatch ctx $
                        Matching.matchingListPrefixWildcard prefixWidth suffixWidth
                  | suffixWidth <- [0, 1, 16, 128, 1200]
                  ]
              , bgroup
                  "capture rest"
                  [ bench ("suffix " <> show suffixWidth) $
                      benchTermCekWithMatch ctx $
                        Matching.matchingListPrefixCaptureRest prefixWidth suffixWidth
                  | suffixWidth <- [0, 1, 16, 128, 1200]
                  ]
              ]
          | prefixWidth <- [0, 1, 3, 16, 128]
          ]
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
          , -- Temporary adversarial cases. Each label records its measured unrestricted Flat size;
            -- keep these uncommitted when the production benchmark changes are separated later.
            mkExhaustionBM "list prefix/zero heads ignored suffix/16383B" $
              Matching.matchingFixpointListPrefixWildcard 0 14531
          , mkExhaustionBM "list prefix/zero heads captured suffix/16383B" $
              Matching.matchingFixpointListPrefixCaptureRest 0 14531
          , mkExhaustionBM "list prefix/three heads ignored suffix/16383B" $
              Matching.matchingFixpointListPrefixWildcard 3 14527
          , mkExhaustionBM "list prefix/three heads captured suffix/16383B" $
              Matching.matchingFixpointListPrefixCaptureRest 3 14527
          , mkExhaustionBM "list prefix/wide wildcard/16383B" $
              Matching.matchingFixpointListPrefixWildcard 9342 0
          , mkExhaustionBM "list prefix/wide captures/16382B" $
              Matching.matchingFixpointListPrefixCaptures 7265 0
          , mkExhaustionBM "list prefix/late mismatch/16383B" $
              Matching.matchingFixpointListPrefixLateMismatch 9339 0
          , mkExhaustionBM "list prefix/too short/16382B" $
              Matching.matchingFixpointListPrefixTooShort 9340
          , mkExhaustionBM "list prefix/nested final head/16382B" $
              Matching.matchingFixpointListPrefixNestedFinal 5943
          , mkExhaustionBM "list prefix/late alternatives 16x1462/16381B" $
              Matching.matchingFixpointListPrefixAlternatives 16 1462 0
          , mkExhaustionBM "list prefix/late alternatives 32x766/16380B" $
              Matching.matchingFixpointListPrefixAlternatives 32 766 0
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
    orderVariants
      | reverseVariants = reverse
      | otherwise = id

{-| Benchmark an experimental 'UPLC.Match' term using the production CEK and the same
machine variant/cost model as 'benchTermCek', but with the 'DefaultUni' matcher enabled
for this invocation only. Ledger evaluation contexts deliberately keep matching disabled
until PLC 1.2 receives a ledger activation. -}
benchTermCekWithMatch :: EvaluationContext -> Term -> Benchmarkable
benchTermCekWithMatch evalCtx term =
  let !term' = force term
   in whnf (either (error . show) (const ()) . evaluateTermWithMatch evalCtx) term'

type MatchParameters =
  MachineParameters
    Cek.CekMachineCosts
    Core.DefaultFun
    (Cek.CekValue Core.DefaultUni Core.DefaultFun ())

evaluateTermWithMatch
  :: EvaluationContext
  -> Term
  -> Either
       ( Cek.CekEvaluationException
           Core.NamedDeBruijn
           Core.DefaultUni
           Core.DefaultFun
       )
       Term
evaluateTermWithMatch evalCtx =
  Cek.cekResultToEither
    . Cek._cekReportResult
    . Cek.runCekDeBruijn (matchParameters evalCtx) Cek.restrictingEnormous Cek.noEmitter

matchParameters :: EvaluationContext -> MatchParameters
matchParameters evalCtx =
  case LedgerApi.toMachineParameters benchmarkProtocolVersion evalCtx of
    MachineParameters caser _matcher variantParameters ->
      MachineParameters caser PLC.availableMatcherBuiltin variantParameters
  where
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
          exhaustionParameters
          (Cek.restricting nearMaximumCpuBudget)
          Cek.noEmitter
          term' of
        Left (Cek.ErrorWithCause (Cek.OperationalError (Cek.CekOutOfExError _)) _) -> ()
        result -> error $ "fixed-point Match did not exhaust its budget: " <> show result
    exhaustionParameters =
      case LedgerApi.toMachineParameters benchmarkProtocolVersion evalCtx of
        MachineParameters caser _matcher variantParameters ->
          MachineParameters caser PLC.availableMatcherBuiltin variantParameters
    -- Keep memory nonbinding to measure the worst latency at the current ledger CPU ceiling.
    nearMaximumCpuBudget = ExRestrictingBudget $ ExBudget 10000000000 1000000000
    benchmarkProtocolVersion = LedgerApi.ledgerLanguageIntroducedIn LedgerApi.PlutusV1

main :: IO ()
main = do
  -- Run each benchmark for at least 15 seconds. Change this with -L or --time-limit. The broad
  -- comparison matrix writes machine-readable results explicitly, so do not create an implicit
  -- HTML report for every process-level repetition.
  configWithReport <- getConfig 15.0
  let config = configWithReport {reportFile = Nothing}
  evalCtx <- evaluate mkMostRecentEvalCtx
  validateComparisons evalCtx
  reverseVariants <- isJust <$> lookupEnv "MATCHING_REVERSE_VARIANTS"
  defaultMainWith config $ benchmarks reverseVariants evalCtx

validateComparisons :: EvaluationContext -> IO ()
validateComparisons evalCtx =
  forM_
    ( Comparison.comparisonCases
        <> Comparison.largeTargetComparisonCases
        <> Comparison.largeTargetAuditCases
    )
    $ \comparison ->
      forM_ (Comparison.comparisonVariants comparison) $ \variant -> do
        let failure detail =
              errorWithoutStackTrace $
                "invalid matching benchmark "
                  <> Comparison.comparisonCaseId comparison
                  <> "/"
                  <> Comparison.comparisonVariantId variant
                  <> ": "
                  <> detail
            term = Comparison.comparisonVariantTerm variant
            chooseDataCount = countChooseData term
            captureCount = countPatternCaptures term
            mechanism = Comparison.comparisonVariantMechanism variant
            expectedCaptureCount =
              Comparison.comparisonCaptures $
                Comparison.comparisonDimensions comparison
            totality =
              Comparison.baselineTotality $
                Comparison.comparisonBaselineMethod comparison
        when
          ( mechanism /= Comparison.MechanismMatch
              && totality == Comparison.BaselinePartial
              && chooseDataCount /= 0
          )
          $ failure
          $ "direct partial baseline unexpectedly contains "
            <> show chooseDataCount
            <> " ChooseData nodes"
        when
          (mechanismRequiresChooseData mechanism && chooseDataCount == 0)
          $ failure "guarded baseline contains no ChooseData node"
        when
          ( mechanism == Comparison.MechanismMatch
              && captureCount /= expectedCaptureCount
          )
          $ failure
          $ "Match contains "
            <> show captureCount
            <> " capture patterns, expected "
            <> show expectedCaptureCount
        case evaluateTermWithMatch evalCtx term of
          Left err -> failure $ "CEK failure: " <> show err
          Right result -> case PLC.readKnownConstant result of
            Left err -> failure $ "non-Integer result: " <> show err
            Right actual
              | actual == Comparison.comparisonExpectedResult comparison -> pure ()
              | otherwise ->
                  failure $
                    "result "
                      <> show (actual :: Integer)
                      <> ", expected "
                      <> show (Comparison.comparisonExpectedResult comparison)

mechanismRequiresChooseData :: Comparison.ComparisonMechanism -> Bool
mechanismRequiresChooseData mechanism = case mechanism of
  Comparison.MechanismChooseDataUnConstrData -> True
  Comparison.MechanismChooseDataUnListData -> True
  Comparison.MechanismChooseDataUnConstrDataUnListData -> True
  Comparison.MechanismChooseDataUnIData -> True
  Comparison.MechanismChooseDataUnIDataEqualsIntegerBuiltinCase -> True
  Comparison.MechanismChooseDataUnBData -> True
  Comparison.MechanismChooseDataUnBDataEqualsByteStringBuiltinCase -> True
  _ -> False

countChooseData :: Term -> Int
countChooseData = \case
  UPLC.Var {} -> 0
  UPLC.LamAbs _ _ body -> countChooseData body
  UPLC.Apply _ fun arg -> countChooseData fun + countChooseData arg
  UPLC.Force _ body -> countChooseData body
  UPLC.Delay _ body -> countChooseData body
  UPLC.Constant {} -> 0
  UPLC.Builtin _ Core.ChooseData -> 1
  UPLC.Builtin {} -> 0
  UPLC.Error {} -> 0
  UPLC.Constr _ _ fields -> sum $ fmap countChooseData fields
  UPLC.Case _ scrutinee branches ->
    countChooseData scrutinee + sum (fmap countChooseData branches)
  UPLC.Match _ scrutinee alternatives ->
    countChooseData scrutinee + sum (fmap (countChooseData . snd) alternatives)

countPatternCaptures :: Term -> Int
countPatternCaptures = \case
  UPLC.Var {} -> 0
  UPLC.LamAbs _ _ body -> countPatternCaptures body
  UPLC.Apply _ fun arg -> countPatternCaptures fun + countPatternCaptures arg
  UPLC.Force _ body -> countPatternCaptures body
  UPLC.Delay _ body -> countPatternCaptures body
  UPLC.Constant {} -> 0
  UPLC.Builtin {} -> 0
  UPLC.Error {} -> 0
  UPLC.Constr _ _ fields -> sum $ fmap countPatternCaptures fields
  UPLC.Case _ scrutinee branches ->
    countPatternCaptures scrutinee + sum (fmap countPatternCaptures branches)
  UPLC.Match _ scrutinee alternatives ->
    countPatternCaptures scrutinee
      + sum
        ( fmap
            ( \(patternToMatch, handler) ->
                countCapturesInPattern patternToMatch + countPatternCaptures handler
            )
            alternatives
        )

countCapturesInPattern :: Core.DefaultBuiltinPattern -> Int
countCapturesInPattern = \case
  Core.DefaultPatternWildcard -> 0
  Core.DefaultPatternCapture -> 1
  Core.DefaultPatternInteger {} -> 0
  Core.DefaultPatternByteString {} -> 0
  Core.DefaultPatternBool {} -> 0
  Core.DefaultPatternUnit -> 0
  Core.DefaultPatternList fieldEnd children ->
    countFieldEndCaptures fieldEnd + sum (fmap countCapturesInPattern children)
  Core.DefaultPatternPair left right ->
    countCapturesInPattern left + countCapturesInPattern right
  Core.DefaultPatternDataConstr _ fieldEnd children ->
    countFieldEndCaptures fieldEnd + sum (fmap countCapturesInPattern children)
  Core.DefaultPatternDataMap fieldEnd children ->
    countFieldEndCaptures fieldEnd + sum (fmap countCapturesInPattern children)
  Core.DefaultPatternDataList fieldEnd children ->
    countFieldEndCaptures fieldEnd + sum (fmap countCapturesInPattern children)
  Core.DefaultPatternDataI child -> countCapturesInPattern child
  Core.DefaultPatternDataB child -> countCapturesInPattern child

countFieldEndCaptures :: Core.DefaultPatternFieldEnd -> Int
countFieldEndCaptures = \case
  Core.DefaultPatternFieldsExact -> 0
  Core.DefaultPatternFieldsPrefixWildcard -> 0
  Core.DefaultPatternFieldsPrefixCapture -> 1
