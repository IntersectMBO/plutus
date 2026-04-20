{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}

module UntypedPlutusCore.Optimize
  ( module Opts
  , optimizeTerm
  , optimizeProgram
  , optimizeProgramWithTrace
  , InlineHints (..)
  , CseWhichSubterms (..)
  , termOptimizer
  , module UntypedPlutusCore.Transform.Optimizer
  ) where

import PlutusCore.Compiler.Types
import PlutusCore.Default qualified as PLC
import PlutusCore.Default.Builtins
import PlutusCore.Name.Unique
import UntypedPlutusCore.Core.Type
import UntypedPlutusCore.Optimize.Opts as Opts
import UntypedPlutusCore.Transform.ApplyToCase (applyToCase)
import UntypedPlutusCore.Transform.CaseOfCase
import UntypedPlutusCore.Transform.CaseReduce
import UntypedPlutusCore.Transform.Cse
import UntypedPlutusCore.Transform.FloatDelay (floatDelay)
import UntypedPlutusCore.Transform.ForceCaseDelay (forceCaseDelay)
import UntypedPlutusCore.Transform.ForceDelay (forceDelay)
import UntypedPlutusCore.Transform.Inline (InlineHints (..), inline)
import UntypedPlutusCore.Transform.LetFloatOut (letFloatOut)
import UntypedPlutusCore.Transform.Optimizer

import Control.Monad
import Data.Either (isRight)
import Data.List as List (foldl')
import Data.Typeable
import Data.Vector.Orphans ()

optimizeProgram
  :: forall name uni fun m a
   . Compiling m uni fun name a
  => OptimizeOpts name a
  -> BuiltinSemanticsVariant fun
  -> Program name uni fun a
  -> m (Program name uni fun a)
optimizeProgram opts builtinSemanticsVariant (Program a v t) =
  Program a v <$> optimizeTerm opts builtinSemanticsVariant t

optimizeProgramWithTrace
  :: forall name uni fun m a
   . Compiling m uni fun name a
  => OptimizeOpts name a
  -> BuiltinSemanticsVariant fun
  -> Program name uni fun a
  -> m (Program name uni fun a, OptimizerTrace name uni fun a)
optimizeProgramWithTrace opts builtinSemanticsVariant (Program a v t) = do
  (result, trace) <-
    runOptimizerT $
      termOptimizer opts builtinSemanticsVariant t
  pure (Program a v result, trace)

optimizeTerm
  :: forall name uni fun m a
   . Compiling m uni fun name a
  => OptimizeOpts name a
  -> BuiltinSemanticsVariant fun
  -> Term name uni fun a
  -> m (Term name uni fun a)
optimizeTerm opts builtinSemanticsVariant term =
  evalOptimizerT $ termOptimizer opts builtinSemanticsVariant term

termOptimizer
  :: forall name uni fun m a
   . Compiling m uni fun name a
  => OptimizeOpts name a
  -> BuiltinSemanticsVariant fun
  -> Term name uni fun a
  -> OptimizerT name uni fun a m (Term name uni fun a)
termOptimizer opts builtinSemanticsVariant =
  simplifyNTimes (_ooMaxSimplifierIterations opts)
    >=> runStage CseStage
    >=> runStage ApplyToCaseStage
  where
    -- Run the simplifier @n@ times
    simplifyNTimes
      :: Int
      -> Term name uni fun a
      -> OptimizerT name uni fun a m (Term name uni fun a)
    simplifyNTimes n = List.foldl' (>=>) pure $ map simplifyStep [1 .. n]

    -- Run CSE @n@ times, interleaved with the simplifier.
    -- See Note [CSE]
    cseNTimes
      :: Int
      -> Term name uni fun a
      -> OptimizerT name uni fun a m (Term name uni fun a)
    cseNTimes n = foldl' (>=>) pure $ concatMap (\i -> [cseStep i, simplifyStep i]) [1 .. n]

    -- generate simplification step
    simplifyStep
      :: Int
      -> Term name uni fun a
      -> OptimizerT name uni fun a m (Term name uni fun a)
    simplifyStep _ =
      runStage FloatDelayStage
        >=> runStage ForceCaseDelayStage
        >=> runStage LetFloatOutStage
        >=> runStage ForceDelayStage
        >=> runStage CaseOfCaseStage
        >=> runStage CaseReduceStage
        >=> runStage InlineStage

    certifiedOnly = _ooCertifiedOptsOnly opts

    runStage stage'
      | certifiedOnly && not certified = pure
      | otherwise = action
      where
        certified = isRight stage'
        action = case stage' of
          FloatDelayStage ->
            floatDelay
          ForceCaseDelayStage ->
            forceCaseDelay
          ForceDelayStage ->
            case (eqT @uni @PLC.DefaultUni, eqT @fun @DefaultFun) of
              (Just Refl, Just Refl) -> forceDelay builtinSemanticsVariant
              _ -> pure
          CaseOfCaseStage ->
            caseOfCase'
          CaseReduceStage ->
            caseReduce
          InlineStage ->
            inline
              (_ooInlineUnconditionalGrowth opts)
              (_ooInlineCallsiteGrowth opts)
              (_ooInlineConstants opts)
              (_ooPreserveLogging opts)
              (_ooInlineHints opts)
              builtinSemanticsVariant
          CseStage ->
            cseNTimes cseTimes
          ApplyToCaseStage ->
            if _ooApplyToCase opts then applyToCase else pure
          LetFloatOutStage ->
            letFloatOut

    caseOfCase'
      :: Term name uni fun a
      -> OptimizerT name uni fun a m (Term name uni fun a)
    caseOfCase' = case eqT @fun @DefaultFun of
      Just Refl -> caseOfCase
      Nothing -> pure

    cseStep
      :: Int
      -> Term name uni fun a
      -> OptimizerT name uni fun a m (Term name uni fun a)
    cseStep _ =
      case (eqT @name @Name, eqT @uni @PLC.DefaultUni) of
        (Just Refl, Just Refl) -> cse (_ooCseWhichSubterms opts) builtinSemanticsVariant
        _ -> pure

    cseTimes = if _ooConservativeOpts opts then 0 else _ooMaxCseIterations opts
