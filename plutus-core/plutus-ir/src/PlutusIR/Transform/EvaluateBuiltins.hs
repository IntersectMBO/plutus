{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}

{-| A pass that tries to evaluate builtin applications in the program.

This functions as a generic constant-folding pass, but which handles
arbitrary builtins. -}
module PlutusIR.Transform.EvaluateBuiltins
  ( evaluateBuiltins
  , evaluateBuiltinsPass
  ) where

import PlutusCore.Builtin
import PlutusIR.Contexts
import PlutusIR.Core

import Control.Lens (transformOf, (^.))
import Data.Functor (void)
import PlutusCore qualified as PLC
import PlutusCore.Name.Unique (HasUnique, TermUnique, TypeUnique)
import PlutusIR.Analysis.Builtins
import PlutusIR.Analysis.VarInfo (VarsInfo, termVarInfo)
import PlutusIR.Pass
import PlutusIR.Purity (isPure)
import PlutusIR.TypeCheck qualified as TC

evaluateBuiltinsPass
  :: (PLC.Typecheckable uni fun, PLC.GEq uni, Applicative m)
  => TC.PirTCConfig uni fun
  -> Bool
  -- ^ Whether to be conservative and try to retain logging behaviour.
  -> BuiltinsInfo uni fun
  -> CostingPart uni fun
  -> Pass m TyName Name uni fun a
evaluateBuiltinsPass tcconfig preserveLogging binfo costModel =
  NamedPass "evaluate builtins" $
    Pass
      (pure . evaluateBuiltins preserveLogging binfo costModel)
      [Typechecks tcconfig]
      [ConstCondition (Typechecks tcconfig)]

evaluateBuiltins
  :: forall tyname name uni fun a
   . ( ToBuiltinMeaning uni fun
     , Typeable tyname
     , Typeable name
     , HasUnique name TermUnique
     , HasUnique tyname TypeUnique
     )
  => Bool
  -- ^ Whether to be conservative and try to retain logging behaviour.
  -> BuiltinsInfo uni fun
  -> CostingPart uni fun
  -> Term tyname name uni fun a
  -> Term tyname name uni fun a
evaluateBuiltins preserveLogging binfo costModel term = transformOf termSubterms processTerm term
  where
    vinfo :: VarsInfo tyname name uni a
    vinfo = termVarInfo term

    -- Nothing means "leave the original term as it was"
    eval
      :: BuiltinRuntime (Term tyname name uni fun ())
      -> AppContext tyname name uni fun a
      -> Maybe (Term tyname name uni fun ())
    eval (BuiltinCostedResult _ getFXs) AppContextEnd =
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
    -- See Note [Evaluating builtins with impure arguments]
    eval (BuiltinExpectArgument toRuntime) (TermAppContext arg _ ctx)
      | isPure binfo vinfo arg =
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

{- Note [Evaluating builtins with impure arguments]

Some builtins take opaque arguments (for documentation on what "opaque" means,
see Note [How to add a built-in function: complicated cases]). By definition,
the values of these arguments are not inspected when evaluating the builtin,
therefore applying the denotation of the builtin will succeed regardless of the
actual values of the arguments. Evaluation order is handled externally, in the
CEK machine, and not in the builtin machinery. Since UPLC is strict, the CEK
machine takes care of evaluating arguments first.

For example, when evaluating `ifThenElse True 7 (divideInteger 1 x)`, the CEK
machine will attempt to evaluate `divideInteger 1 x` before applying `ifThenElse`.
Of course, when `x` is `0` evaluation fails and the program reduces to `error`.

However, when constant folding at compile time, there may not be a concrete
value for `x` yet. Since a builtin taking opaque arguments does not inspect them,
applying its denotation will succeed regardless of their actual values.
This is not sound in a strict language, and we can preserve the correct order of
side effects by only folding a builtin when its arguments are pure.
-}
