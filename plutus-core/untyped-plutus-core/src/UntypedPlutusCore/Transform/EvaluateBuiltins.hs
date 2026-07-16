{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}

{-| This module mirrors 'PlutusIR.Transform.EvaluateBuiltins', adapted for UPLC's
untyped 'Term' and 'AppCtx'. See that module for detailed commentary. -}
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
  :: (Monad m, ToBuiltinMeaning uni fun, Typeable name, Typeable pat)
  => Bool
  -- ^ Whether to be conservative and try to retain logging behaviour.
  -> BuiltinsInfo uni fun
  -> CostingPart uni fun
  -> Term name uni fun pat a
  -> OptimizerT name uni fun pat a m (Term name uni fun pat a)
evaluateBuiltinsPass preserveLogging binfo costModel term = do
  result <- evaluateBuiltins preserveLogging binfo costModel term
  recordOptimization term ConstantFoldingStage result
  return result

evaluateBuiltins
  :: forall m name uni fun pat a
   . ( Monad m
     , ToBuiltinMeaning uni fun
     , Typeable name
     , Typeable pat
     )
  => Bool
  -- ^ Whether to be conservative and try to retain logging behaviour.
  -> BuiltinsInfo uni fun
  -> CostingPart uni fun
  -> Term name uni fun pat a
  -> OptimizerT name uni fun pat a m (Term name uni fun pat a)
evaluateBuiltins preserveLogging binfo costModel =
  pure . transformOf termSubterms processTerm
  where
    eval
      :: BuiltinRuntime (Term name uni fun pat ())
      -> AppCtx name uni fun pat a
      -> Maybe (Term name uni fun pat ())
    eval (BuiltinCostedResult _ getFXs) AppCtxEnd =
      case getFXs of
        BuiltinSuccess y -> Just y
        BuiltinSuccessWithLogs _ y -> if preserveLogging then Nothing else Just y
        BuiltinFailure {} -> Nothing
    eval (BuiltinExpectArgument toRuntime) (AppCtxTerm _ arg ctx) =
      eval (toRuntime $ void arg) ctx
    eval (BuiltinExpectForce runtime) (AppCtxType _ ctx) =
      eval runtime ctx
    eval _ _ = Nothing

    processTerm :: Term name uni fun pat a -> Term name uni fun pat a
    -- See Note [Context splitting in a recursive pass]
    processTerm t@(splitAppCtx -> (Builtin x bn, argCtx)) =
      let runtime = toBuiltinRuntime costModel (toBuiltinMeaning (binfo ^. biSemanticsVariant) bn)
       in case eval runtime argCtx of
            -- See Note [Unserializable constants] in PlutusIR.Analysis.Builtins
            Just t' | termIsSerializable binfo t' -> x <$ t'
            _ -> t
    processTerm t = t
