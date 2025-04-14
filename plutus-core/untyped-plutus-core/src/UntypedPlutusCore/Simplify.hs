{-# LANGUAGE GADTs            #-}
{-# LANGUAGE RankNTypes       #-}
{-# LANGUAGE TypeApplications #-}

module UntypedPlutusCore.Simplify (
    module Opts,
    simplifyTerm,
    simplifyProgram,
    simplifyProgramWithTrace,
    InlineHints (..),
) where

import PlutusCore.Compiler.Types
import PlutusCore.Default qualified as PLC
import PlutusCore.Default.Builtins
import PlutusCore.Name.Unique
import UntypedPlutusCore.Core.Type
import UntypedPlutusCore.Simplify.Opts as Opts
import UntypedPlutusCore.Transform.CaseOfCase
import UntypedPlutusCore.Transform.CaseReduce
import UntypedPlutusCore.Transform.Cse
import UntypedPlutusCore.Transform.DelayForce (delayForce)
import UntypedPlutusCore.Transform.FloatDelay (floatDelay)
import UntypedPlutusCore.Transform.ForceDelay (forceDelay)
import UntypedPlutusCore.Transform.Inline (InlineHints (..), inline)
import UntypedPlutusCore.Transform.Simplifier

import Control.Monad
import Data.List as List (foldl')
import Data.Typeable
import Data.Vector.Orphans ()

simplifyProgram ::
    forall name uni fun m a.
    (Compiling m uni fun name a) =>
    SimplifyOpts name a ->
    BuiltinSemanticsVariant fun ->
    Program name uni fun a ->
    m (Program name uni fun a)
simplifyProgram opts builtinSemanticsVariant (Program a v t) =
  Program a v <$> simplifyTerm opts builtinSemanticsVariant t

simplifyProgramWithTrace ::
    forall name uni fun m a.
    (Compiling m uni fun name a) =>
    SimplifyOpts name a ->
    BuiltinSemanticsVariant fun ->
    Program name uni fun a ->
    m (Program name uni fun a, SimplifierTrace name uni fun a)
simplifyProgramWithTrace opts builtinSemanticsVariant (Program a v t) = do
  (result, trace) <-
    runSimplifierT
      $ termSimplifier opts builtinSemanticsVariant t
  pure (Program a v result, trace)

simplifyTerm ::
    forall name uni fun m a.
    (Compiling m uni fun name a) =>
    SimplifyOpts name a ->
    BuiltinSemanticsVariant fun ->
    Term name uni fun a ->
    m (Term name uni fun a)
simplifyTerm opts builtinSemanticsVariant term =
  evalSimplifierT $ termSimplifier opts builtinSemanticsVariant term

termSimplifier ::
    forall name uni fun m a.
    (Compiling m uni fun name a) =>
    SimplifyOpts name a ->
    BuiltinSemanticsVariant fun ->
    Term name uni fun a ->
    SimplifierT name uni fun a m (Term name uni fun a)
termSimplifier opts builtinSemanticsVariant =
    stage1NTimes (_soMaxSimplifierIterations opts) >=> stage2NTimes cseTimes
  where
    -- Run the simplifier @n@ times
    stage1NTimes ::
      Int ->
      Term name uni fun a ->
      SimplifierT name uni fun a m (Term name uni fun a)
    stage1NTimes n = List.foldl' (>=>) pure $ replicate n simplifyStep

    -- Run delay-force and CSE @n@ times, interleaved with the simplifier.
    -- See Note [CSE].
    -- We put 'delayForce' here instead of 'stage1NTimes', because experiments showed that
    -- spending @force@s 'forceDelay' results
    stage2NTimes ::
      Int ->
      Term name uni fun a ->
      SimplifierT name uni fun a m (Term name uni fun a)
    stage2NTimes n = foldl' (>=>) pure . concat $ replicate n [delayForce, cseStep, simplifyStep]

    -- generate simplification step
    simplifyStep ::
      Term name uni fun a ->
      SimplifierT name uni fun a m (Term name uni fun a)
    simplifyStep =
        floatDelay
        >=> case (eqT @uni @PLC.DefaultUni, eqT @fun @DefaultFun) of
            (Just Refl, Just Refl) -> forceDelay builtinSemanticsVariant
            _                      -> pure
        >=> caseOfCase'
        >=> caseReduce
        >=> inline
              (_soInlineCallsiteGrowth opts)
              (_soInlineConstants opts)
              (_soInlineHints opts)
              builtinSemanticsVariant

    caseOfCase' ::
      Term name uni fun a ->
      SimplifierT name uni fun a m (Term name uni fun a)
    caseOfCase' = case eqT @fun @DefaultFun of
      Just Refl -> caseOfCase
      Nothing   -> pure

    cseStep ::
      Term name uni fun a ->
      SimplifierT name uni fun a m (Term name uni fun a)
    cseStep =
      case (eqT @name @Name, eqT @uni @PLC.DefaultUni) of
        (Just Refl, Just Refl) -> cse builtinSemanticsVariant
        _                      -> pure

    cseTimes = if _soConservativeOpts opts then 0 else _soMaxCseIterations opts
