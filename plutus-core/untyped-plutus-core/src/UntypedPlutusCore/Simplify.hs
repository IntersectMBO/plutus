{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}

module UntypedPlutusCore.Simplify
  ( module Opts
  , simplifyTerm
  , simplifyProgram
  , simplifyProgramWithTrace
  , InlineHints (..)
  , CseWhichSubterms (..)
  , termSimplifier
  , module UntypedPlutusCore.Transform.Simplifier
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
import UntypedPlutusCore.Transform.FloatDelay (floatDelay)
import UntypedPlutusCore.Transform.ForceCaseDelay (forceCaseDelay)
import UntypedPlutusCore.Transform.ForceDelay (forceDelay)
import UntypedPlutusCore.Transform.Inline (InlineHints (..), inline)
import UntypedPlutusCore.Transform.Simplifier

import Control.Monad
import Data.List as List (foldl')
import Data.Typeable
import Data.Vector.Orphans ()

simplifyProgram
  :: forall name uni fun m a
   . Compiling m uni fun name a
  => SimplifyOpts name a
  -> BuiltinSemanticsVariant fun
  -> Program name uni fun a
  -> m (Program name uni fun a)
simplifyProgram opts builtinSemanticsVariant (Program a v t) =
  Program a v <$> simplifyTerm opts builtinSemanticsVariant t

simplifyProgramWithTrace
  :: forall name uni fun m a
   . Compiling m uni fun name a
  => SimplifyOpts name a
  -> BuiltinSemanticsVariant fun
  -> Program name uni fun a
  -> m (Program name uni fun a, SimplifierTrace name uni fun a)
simplifyProgramWithTrace opts builtinSemanticsVariant (Program a v t) = do
  (result, trace) <-
    runSimplifierT $
      termSimplifier opts builtinSemanticsVariant t
  pure (Program a v result, trace)

simplifyTerm
  :: forall name uni fun m a
   . Compiling m uni fun name a
  => SimplifyOpts name a
  -> BuiltinSemanticsVariant fun
  -> Term name uni fun a
  -> m (Term name uni fun a)
simplifyTerm opts builtinSemanticsVariant term =
  evalSimplifierT $ termSimplifier opts builtinSemanticsVariant term

termSimplifier
  :: forall name uni fun m a
   . Compiling m uni fun name a
  => SimplifyOpts name a
  -> BuiltinSemanticsVariant fun
  -> Term name uni fun a
  -> SimplifierT name uni fun a m (Term name uni fun a)
termSimplifier opts builtinSemanticsVariant =
  simplifyNTimes (_soMaxSimplifierIterations opts) >=> cseNTimes cseTimes
  where
    -- Run the simplifier @n@ times
    simplifyNTimes
      :: Int
      -> Term name uni fun a
      -> SimplifierT name uni fun a m (Term name uni fun a)
    simplifyNTimes n = List.foldl' (>=>) pure $ map simplifyStep [1 .. n]

    -- Run CSE @n@ times, interleaved with the simplifier.
    -- See Note [CSE]
    cseNTimes
      :: Int
      -> Term name uni fun a
      -> SimplifierT name uni fun a m (Term name uni fun a)
    cseNTimes n = foldl' (>=>) pure $ concatMap (\i -> [cseStep i, simplifyStep i]) [1 .. n]

    -- generate simplification step
    simplifyStep
      :: Int
      -> Term name uni fun a
      -> SimplifierT name uni fun a m (Term name uni fun a)
    simplifyStep _ =
      floatDelay
        >=> forceCaseDelay
        >=> case (eqT @uni @PLC.DefaultUni, eqT @fun @DefaultFun) of
          (Just Refl, Just Refl) -> forceDelay builtinSemanticsVariant
          _ -> pure
        >=> caseOfCase'
        >=> caseReduce
        >=> inline
          (_soInlineCallsiteGrowth opts)
          (_soInlineConstants opts)
          (_soPreserveLogging opts)
          (_soInlineHints opts)
          builtinSemanticsVariant

    caseOfCase'
      :: Term name uni fun a
      -> SimplifierT name uni fun a m (Term name uni fun a)
    caseOfCase' = case eqT @fun @DefaultFun of
      Just Refl -> caseOfCase
      Nothing -> pure

    cseStep
      :: Int
      -> Term name uni fun a
      -> SimplifierT name uni fun a m (Term name uni fun a)
    cseStep _ =
      case (eqT @name @Name, eqT @uni @PLC.DefaultUni) of
        (Just Refl, Just Refl) -> cse (_soCseWhichSubterms opts) builtinSemanticsVariant
        _ -> pure

    cseTimes = if _soConservativeOpts opts then 0 else _soMaxCseIterations opts
