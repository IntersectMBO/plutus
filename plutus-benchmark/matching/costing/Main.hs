{-# LANGUAGE BangPatterns #-}

-- | Criterion driver for exact Match-cost calibration workloads.
module Main (main) where

import Control.DeepSeq (force)
import Control.Exception (evaluate)
import Control.Monad (forM_)
import Criterion.Main
import Criterion.Types (Config (..))
import PlutusBenchmark.Common (Term, getConfig, mkMostRecentEvalCtx)
import PlutusBenchmark.Matching.Costing
  ( CostingCase (..)
  , MatchStepCounts (..)
  , Unit (..)
  , calibrationCases
  )
import PlutusCore qualified as Core
import PlutusCore.Builtin qualified as PLC
import PlutusCore.Evaluation.Machine.ExBudget (ExBudget (..))
import PlutusCore.Evaluation.Machine.MachineParameters
  ( MachineParameters (..)
  , MachineVariantParameters (..)
  )
import PlutusLedgerApi.Common (EvaluationContext)
import PlutusLedgerApi.Common qualified as LedgerApi
import System.Mem (performGC)
import UntypedPlutusCore.Evaluation.Machine.Cek qualified as Cek
import UntypedPlutusCore.Evaluation.Machine.Cek.CekMachineCosts
  ( unitCekMachineCosts
  )

data MatchStepBudgets = MatchStepBudgets
  { matchBudget :: !ExBudget
  , patternBudget :: !ExBudget
  , structuralBudget :: !ExBudget
  , nextBudget :: !ExBudget
  , caseBudget :: !ExBudget
  , lamBudget :: !ExBudget
  }
  deriving stock (Eq, Show)

instance Semigroup MatchStepBudgets where
  MatchStepBudgets m p s n k l
    <> MatchStepBudgets m' p' s' n' k' l' =
      MatchStepBudgets
        (m <> m')
        (p <> p')
        (s <> s')
        (n <> n')
        (k <> k')
        (l <> l')

instance Monoid MatchStepBudgets where
  mempty =
    MatchStepBudgets
      mempty
      mempty
      mempty
      mempty
      mempty
      mempty

type MatchParameters =
  MachineParameters
    Cek.CekMachineCosts
    Core.DefaultFun
    (Cek.CekValue Core.DefaultUni Core.DefaultFun ())

main :: IO ()
main = do
  configWithReport <- getConfig 15.0
  let config = configWithReport {reportFile = Nothing}
  evalCtx <- evaluate mkMostRecentEvalCtx
  let !cases = calibrationCases
  validateCases evalCtx cases
  -- Validation constructs one term at a time. Collect its final term before Criterion starts so
  -- the measured suite retains only the environment for the benchmark currently being sampled.
  performGC
  defaultMainWith
    config
    [ bgroup "matching-costing-four-kind" $
        fmap (benchmarkCase evalCtx) cases
    ]

benchmarkCase :: EvaluationContext -> CostingCase -> Benchmark
benchmarkCase evalCtx costingCase =
  env (evaluate . force $ costingCaseTerm costingCase Unit) $ \ ~term ->
    bench (costingCaseName costingCase) $
      whnf (evaluateTermWithMatch evalCtx) term

evaluateTermWithMatch :: EvaluationContext -> Term -> ()
evaluateTermWithMatch evalCtx =
  either (error . show) (const ())
    . Cek.cekResultToEither
    . Cek._cekReportResult
    . Cek.runCekDeBruijn (matchParameters evalCtx) Cek.restrictingEnormous Cek.noEmitter

matchParameters :: EvaluationContext -> MatchParameters
matchParameters evalCtx =
  case LedgerApi.toMachineParameters benchmarkProtocolVersion evalCtx of
    MachineParameters caser _matcher variantParameters ->
      MachineParameters caser PLC.availableMatcherBuiltin variantParameters
  where
    -- Keep this aligned with PlutusBenchmark.Common.evaluateCekLikeInProd.
    benchmarkProtocolVersion = LedgerApi.ledgerLanguageIntroducedIn LedgerApi.PlutusV1

unitMatchParameters :: EvaluationContext -> MatchParameters
unitMatchParameters evalCtx =
  case matchParameters evalCtx of
    MachineParameters caser matcher (MachineVariantParameters _ runtime) ->
      MachineParameters
        caser
        matcher
        (MachineVariantParameters unitCekMachineCosts runtime)

matchStepBudgeting
  :: Cek.ExBudgetMode
       MatchStepBudgets
       Core.DefaultUni
       Core.DefaultFun
matchStepBudgeting =
  Cek.monoidalBudgeting $ \category budget -> case category of
    Cek.BStep Cek.BMatch -> mempty {matchBudget = budget}
    Cek.BStep Cek.BPattern -> mempty {patternBudget = budget}
    Cek.BStep Cek.BStructural -> mempty {structuralBudget = budget}
    Cek.BStep Cek.BMatchNext -> mempty {nextBudget = budget}
    Cek.BStep Cek.BCase -> mempty {caseBudget = budget}
    Cek.BStep Cek.BLamAbs -> mempty {lamBudget = budget}
    _ -> mempty

validateCases :: EvaluationContext -> [CostingCase] -> IO ()
validateCases evalCtx cases =
  forM_ cases $ \costingCase -> do
    term <- evaluate . force $ costingCaseTerm costingCase Unit
    let report =
          Cek.runCekDeBruijn
            (unitMatchParameters evalCtx)
            matchStepBudgeting
            Cek.noEmitter
            term
    case Cek.cekResultToEither $ Cek._cekReportResult report of
      Left err ->
        errorWithoutStackTrace $
          "costing case " <> costingCaseName costingCase <> " failed: " <> show err
      Right _ ->
        let expected = budgetsFromCounts $ costingCaseExpected costingCase
            actual = Cek._cekReportCost report
         in if actual == expected
              then pure ()
              else
                errorWithoutStackTrace $
                  "costing case "
                    <> costingCaseName costingCase
                    <> " has the wrong Match-step counts: expected "
                    <> show expected
                    <> ", got "
                    <> show actual

budgetsFromCounts :: MatchStepCounts -> MatchStepBudgets
budgetsFromCounts (MatchStepCounts m c f b w e container pair s dispatch n k l) =
  MatchStepBudgets
    (unit $ m + c)
    ( unit $
        m
          + 2 * f
          + 10 * b
          + 2 * e
          + 7 * container
          + 6 * pair
          + 6 * dispatch
          + 4 * n
    )
    (unit s)
    (unit $ w + e + n)
    (unit k)
    (unit l)
  where
    unit count = ExBudget (fromIntegral count) 0
