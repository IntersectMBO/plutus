{-# LANGUAGE TypeApplications #-}

module PlutusCore.Executable.Eval where

import PlutusLedgerApi.Common
import UntypedPlutusCore qualified as UPLC
import UntypedPlutusCore.Evaluation.Machine.Cek
import UntypedPlutusCore.Transform.Certify.Trace

import PlutusCore.Builtin (CaserBuiltin)
import PlutusCore.Default (BuiltinSemanticsVariant)
import PlutusCore.Evaluation.Machine.ExBudgetingDefaults qualified as PLC
import PlutusCore.Version qualified as PLC
import PlutusPrelude (unsafeFromRight)
import UntypedPlutusCore.DeBruijn (FreeVariableError)

import Data.Bifunctor (first)
import Data.Foldable qualified as F
import Data.Functor (void)

-- | Evaluate a single term in counting mode.
evalCounting
  :: EvaluationContext
  -> MajorProtocolVersion
  -> PLC.Version
  -> UPLC.Term UPLC.NamedDeBruijn UPLC.DefaultUni UPLC.DefaultFun ()
  -> ( Either
         (CekEvaluationException UPLC.NamedDeBruijn UPLC.DefaultUni UPLC.DefaultFun)
         (UPLC.Term UPLC.NamedDeBruijn UPLC.DefaultUni UPLC.DefaultFun ())
     , ExBudget
     )
evalCounting evalCtx pv plcVersion term =
  ( cekResultToEither (_cekReportResult report)
  , let CountingSt cost = _cekReportCost report in cost
  )
  where
    report = evaluateTerm counting pv plcVersion Quiet evalCtx term

standaloneCaserBuiltin :: PLC.Version -> CaserBuiltin UPLC.DefaultUni
standaloneCaserBuiltin = defaultCaserBuiltinFor newestPV

-- | Build a default evaluation context for a given semantics variant.
mkDefaultEvalCtx
  :: BuiltinSemanticsVariant UPLC.DefaultFun -> EvaluationContext
mkDefaultEvalCtx semvar =
  case PLC.defaultCostModelParamsForVariant semvar of
    Just p ->
      either (error . show) id $
        mkDynEvaluationContext
          PlutusV3
          defaultCaserBuiltinFor
          [semvar]
          (const semvar)
          p
    Nothing ->
      error $ "Couldn't get cost model params for " <> show semvar

{-| Evaluate all ASTs in the trace, each applied to the given arguments arguments,
in counting mode. Returns @(Maybe error, budget)@. -}
evalOptimizerTrace
  :: EvaluationContext
  -> PLC.Version
  -> OptimizerTrace UPLC.Name UPLC.DefaultUni UPLC.DefaultFun a
  -> [UPLC.Term UPLC.NamedDeBruijn UPLC.DefaultUni UPLC.DefaultFun ()]
  -- ^ Arguments to apply to each AST before evaluation
  -> [ ( Maybe
           (CekEvaluationException UPLC.NamedDeBruijn UPLC.DefaultUni UPLC.DefaultFun)
       , ExBudget
       )
     ]
evalOptimizerTrace evalCtx plcVersion trace args =
  first (either Just (const Nothing)) . evalCounting evalCtx newestPV plcVersion
    <$> appliedTerms
  where
    appliedTerms :: [UPLC.Term UPLC.NamedDeBruijn UPLC.DefaultUni UPLC.DefaultFun ()]
    appliedTerms =
      ( \ast ->
          F.foldl'
            UPLC.applyTerm
            ( unsafeFromRight @FreeVariableError $
                UPLC.deBruijnTerm (void ast)
            )
            args
      )
        <$> allASTs trace

{- TODO: This is an exact copy of some code in `PlutusBenchmark.Common`.  Check
 if we can use this version in plutus-benchmark without affecting the
 benchmark results (initial experiments were unclear). -}
{-| Evaluate a term as it would be evaluated using the on-chain evaluator,
at the most recent protocol version with restrictingEnormous budget mode
(no budget tracking overhead). Suitable for timing. -}
evaluateCekLikeInProd
  :: EvaluationContext
  -> PLC.Version
  -> UPLC.Term UPLC.NamedDeBruijn UPLC.DefaultUni UPLC.DefaultFun ()
  -> Either
       (CekEvaluationException UPLC.NamedDeBruijn UPLC.DefaultUni UPLC.DefaultFun)
       (UPLC.Term UPLC.NamedDeBruijn UPLC.DefaultUni UPLC.DefaultFun ())
evaluateCekLikeInProd evalCtx plcVersion term =
  cekResultToEither . _cekReportResult $
    evaluateTerm restrictingEnormous newestPV plcVersion Quiet evalCtx term

{-| Evaluate a single program term applied to arguments in counting mode.
Returns @(Maybe error, budget)@. -}
evalCountingWithArgs
  :: EvaluationContext
  -> PLC.Version
  -> UPLC.Term UPLC.Name UPLC.DefaultUni UPLC.DefaultFun ()
  -- ^ Main program
  -> [UPLC.Term UPLC.NamedDeBruijn UPLC.DefaultUni UPLC.DefaultFun ()]
  -- ^ Arguments
  -> ( Maybe
         (CekEvaluationException UPLC.NamedDeBruijn UPLC.DefaultUni UPLC.DefaultFun)
     , ExBudget
     )
evalCountingWithArgs evalCtx plcVersion term args =
  let dbTerm =
        unsafeFromRight @FreeVariableError $
          UPLC.deBruijnTerm term
      applied = F.foldl' UPLC.applyTerm dbTerm args
   in first (either Just (const Nothing)) $ evalCounting evalCtx newestPV plcVersion applied
