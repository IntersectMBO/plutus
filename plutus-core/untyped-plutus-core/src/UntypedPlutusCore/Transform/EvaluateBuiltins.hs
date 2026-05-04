{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}

module UntypedPlutusCore.Transform.EvaluateBuiltins
  ( evaluateBuiltinsPass
  ) where

import PlutusCore.Builtin
import UntypedPlutusCore.Analysis.Builtins
import UntypedPlutusCore.Contexts
import UntypedPlutusCore.Core
import UntypedPlutusCore.Transform.Certify.Trace
import UntypedPlutusCore.Transform.Optimizer

import Control.Lens (transformOf, (^.))
import Data.Functor (void)

evaluateBuiltinsPass
  :: (Monad m, ToBuiltinMeaning uni fun, Typeable name)
  => Bool
  -- ^ Whether to be conservative and try to retain logging behaviour.
  -> BuiltinsInfo uni fun
  -> CostingPart uni fun
  -> Term name uni fun a
  -> OptimizerT name uni fun a m (Term name uni fun a)
evaluateBuiltinsPass preserveLogging binfo costModel term = do
  result <- evaluateBuiltins preserveLogging binfo costModel term
  recordOptimization term ConstantFoldingStage result
  return result

evaluateBuiltins
  :: forall m name uni fun a
   . ( Monad m
     , ToBuiltinMeaning uni fun
     , Typeable name
     )
  => Bool
  -- ^ Whether to be conservative and try to retain logging behaviour.
  -> BuiltinsInfo uni fun
  -> CostingPart uni fun
  -> Term name uni fun a
  -> OptimizerT name uni fun a m (Term name uni fun a)
evaluateBuiltins preserveLogging binfo costModel =
  pure . transformOf termSubterms processTerm
  where
    -- Nothing means "leave the original term as it was"
    eval
      :: BuiltinRuntime (Term name uni fun ())
      -> AppCtx name uni fun a
      -> Maybe (Term name uni fun ())
    eval (BuiltinCostedResult _ getFXs) AppCtxEnd =
      case getFXs of
        BuiltinSuccess y -> Just y
        -- Evaluates successfully, but does logging. If we're being conservative
        -- then we should leave these in, so we don't remove people's logging!
        -- Otherwise `trace "hello" x` is a prime candidate for evaluation!
        BuiltinSuccessWithLogs _ y -> if preserveLogging then Nothing else Just y
        -- Evaluation failure. This can mean that the evaluation legitimately
        -- failed (e.g. `divideInteger 1 0`), or that it failed because the
        -- argument terms are not currently in the right form (because they're
        -- not evaluated, we're in the middle of a term here!). Since we can't
        -- distinguish these, we have to assume it's the latter case and just leave
        -- things alone.
        BuiltinFailure {} -> Nothing
    eval (BuiltinExpectArgument toRuntime) (AppCtxTerm _ arg ctx) =
      -- Builtin evaluation does not work with annotations, so we have to throw
      -- the argument annotation away here
      eval (toRuntime $ void arg) ctx
    eval (BuiltinExpectForce runtime) (AppCtxType _ ctx) =
      eval runtime ctx
    -- arg mismatch, including under-application, just leave it alone
    eval _ _ = Nothing

    processTerm :: Term name uni fun a -> Term name uni fun a
    -- See Note [Context splitting in a recursive pass]
    processTerm t@(splitAppCtx -> (Builtin x bn, argCtx)) =
      let runtime = toBuiltinRuntime costModel (toBuiltinMeaning (binfo ^. biSemanticsVariant) bn)
       in case eval runtime argCtx of
            -- Builtin evaluation gives us a fresh term with no annotation.
            -- Use the annotation of the builtin node, arbitrarily. This is slightly
            -- suboptimal, e.g. in `ifThenElse True x y`, we will get back `x`, but
            -- with the annotation that was on the `ifThenElse` node. But we can't
            -- easily do better.
            -- See Note [Unserializable constants]
            Just t' | termIsSerializable binfo t' -> x <$ t'
            _ -> t
    processTerm t = t
