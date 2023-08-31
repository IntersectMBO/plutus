{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns        #-}
-- | A pass that tries to evaluate builtin applications in the program.
--
-- This functions as a generic constant-folding pass, but which handles
-- arbitrary builtins.
module PlutusIR.Transform.EvaluateBuiltins
    ( evaluateBuiltins
    ) where

import PlutusCore.Builtin
import PlutusIR.Contexts
import PlutusIR.Core

import Control.Lens (transformOf)
import Data.Functor (void)

evaluateBuiltins
  :: forall tyname name uni fun a
  . (ToBuiltinMeaning uni fun
  , Typeable tyname
  , Typeable name)
  => Bool
  -- ^ Whether to be conservative and try to retain logging behaviour.
  -> BuiltinSemanticsVariant fun
  -> CostingPart uni fun
  -> Term tyname name uni fun a
  -> Term tyname name uni fun a
evaluateBuiltins conservative semvar costModel = transformOf termSubterms processTerm
  where
    -- Nothing means "leave the original term as it was"
    eval
      :: BuiltinRuntime (Term tyname name uni fun ())
      -> AppContext tyname name uni fun a
      -> Maybe (Term tyname name uni fun ())
    eval (BuiltinResult _ getX) AppContextEnd =
        case getX of
            MakeKnownSuccess v           -> Just v
            -- Evaluates successfully, but does logging. If we're being conservative
            -- then we should leave these in, so we don't remove people's logging!
            -- Otherwise `trace "hello" x` is a prime candidate for evaluation!
            MakeKnownSuccessWithLogs _ v -> if conservative then Nothing else Just v
            -- Evaluation failure. This can mean that the evaluation legitimately
            -- failed (e.g. `divideInteger 1 0`), or that it failed because the
            -- argument terms are not currently in the right form (because they're
            -- not evaluated, we're in the middle of a term here!). Since we can't
            -- distinguish these, we have to assume it's the latter case and just leave
            -- things alone.
            MakeKnownFailure{}           -> Nothing
    eval (BuiltinExpectArgument toRuntime) (TermAppContext arg _ ctx) =
        -- Builtin evaluation does not work with annotations, so we have to throw
        -- the argument annotation away here
        eval (toRuntime $ void arg) ctx
    eval (BuiltinExpectForce runtime) (TypeAppContext _ _ ctx) =
        eval runtime ctx
    -- arg mismatch, including under-application, just leave it alone
    eval _ _ = Nothing

    processTerm :: Term tyname name uni fun a -> Term tyname name uni fun a
    -- See Note [Context splitting in a recursive pass]
    processTerm t@(splitApplication -> (Builtin x bn, argCtx)) =
      let runtime = toBuiltinRuntime costModel (toBuiltinMeaning semvar bn)
      in case eval runtime argCtx of
           -- Builtin evaluation gives us a fresh term with no annotation.
           -- Use the annotation of the builtin node, arbitrarily. This is slightly
           -- suboptimal, e.g. in `ifThenElse True x y`, we will get back `x`, but
           -- with the annotation that was on the `ifThenElse` node. But we can't
           -- easily do better.
           Just t' -> x <$ t'
           Nothing -> t
    processTerm t = t
