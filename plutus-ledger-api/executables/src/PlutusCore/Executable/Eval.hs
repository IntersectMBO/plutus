{-# LANGUAGE TypeApplications #-}

module PlutusCore.Executable.Eval where

import PlutusLedgerApi.Common
import UntypedPlutusCore qualified as UPLC
import UntypedPlutusCore.Evaluation.Machine.Cek
import UntypedPlutusCore.Transform.Certify.Trace

import PlutusCore.Builtin qualified as PLC
import PlutusCore.Default (BuiltinSemanticsVariant)
import PlutusCore.Evaluation.Machine.ExBudgetingDefaults qualified as PLC
import PlutusPrelude (unsafeFromRight)
import UntypedPlutusCore.DeBruijn (FreeVariableError)

import Data.Bifunctor (first)
import Data.Foldable qualified as F
import Data.Functor (void)

-- | Evaluate a single term in counting mode.
evalCounting
  :: EvaluationContext
  -> MajorProtocolVersion
  -> UPLC.Term UPLC.NamedDeBruijn UPLC.DefaultUni UPLC.DefaultFun ()
  -> ( Either
         (CekEvaluationException UPLC.NamedDeBruijn UPLC.DefaultUni UPLC.DefaultFun)
         (UPLC.Term UPLC.NamedDeBruijn UPLC.DefaultUni UPLC.DefaultFun ())
     , ExBudget
     )
evalCounting evalCtx pv term =
  ( cekResultToEither (_cekReportResult report)
  , let CountingSt cost = _cekReportCost report in cost
  )
  where
    report = evaluateTerm counting pv Quiet evalCtx term

-- | Build a default evaluation context for a given semantics variant.
mkDefaultEvalCtx
  :: BuiltinSemanticsVariant UPLC.DefaultFun -> EvaluationContext
mkDefaultEvalCtx semvar =
  case PLC.defaultCostModelParamsForVariant semvar of
    Just p ->
      either (error . show) id $
        mkDynEvaluationContext
          PlutusV3
          (\_ -> PLC.CaserBuiltin PLC.caseBuiltin)
          [semvar]
          (const semvar)
          p
    Nothing ->
      error $ "Couldn't get cost model params for " <> show semvar

{-| Evaluate all ASTs in the trace, each applied to the given arguments arguments,
in counting mode. Returns @(Maybe error, budget)@. -}
evalSimplifierTrace
  :: EvaluationContext
  -> SimplifierTrace UPLC.Name UPLC.DefaultUni UPLC.DefaultFun a
  -> [UPLC.Term UPLC.NamedDeBruijn UPLC.DefaultUni UPLC.DefaultFun ()]
  -- ^ Arguments to apply to each AST before evaluation
  -> [ ( Maybe
           (CekEvaluationException UPLC.NamedDeBruijn UPLC.DefaultUni UPLC.DefaultFun)
       , ExBudget
       )
     ]
evalSimplifierTrace evalCtx trace args =
  first (either Just (const Nothing)) . evalCounting evalCtx newestPV
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

{-| Evaluate a single program term applied to arguments in counting mode.
Returns @(Maybe error, budget)@. -}
evalCountingWithArgs
  :: EvaluationContext
  -> UPLC.Term UPLC.Name UPLC.DefaultUni UPLC.DefaultFun ()
  -- ^ Main program
  -> [UPLC.Term UPLC.NamedDeBruijn UPLC.DefaultUni UPLC.DefaultFun ()]
  -- ^ Arguments
  -> ( Maybe
         (CekEvaluationException UPLC.NamedDeBruijn UPLC.DefaultUni UPLC.DefaultFun)
     , ExBudget
     )
evalCountingWithArgs evalCtx term args =
  let dbTerm =
        unsafeFromRight @FreeVariableError $
          UPLC.deBruijnTerm term
      applied = F.foldl' UPLC.applyTerm dbTerm args
   in first (either Just (const Nothing)) $ evalCounting evalCtx newestPV applied
