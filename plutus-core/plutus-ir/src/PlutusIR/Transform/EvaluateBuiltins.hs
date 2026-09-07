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

import Control.Lens (preview, transformOf, (^.))
import Data.Functor (void)
import Data.Map qualified as Map
import PlutusCore qualified as PLC
import PlutusIR.Analysis.Builtins
import PlutusIR.Pass
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
     )
  => Bool
  -- ^ Whether to be conservative and try to retain logging behaviour.
  -> BuiltinsInfo uni fun
  -> CostingPart uni fun
  -> Term tyname name uni fun a
  -> Term tyname name uni fun a
evaluateBuiltins preserveLogging binfo costModel = transformOf termSubterms processTerm
  where
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
      let runtime = toBuiltinRuntime costModel (toBuiltinMeaning (binfo ^. biSemanticsVariant) bn)
       in case eval runtime argCtx of
            -- Builtin evaluation gives us a fresh term with no annotation.
            -- Use the annotation of the builtin node, arbitrarily. This is slightly
            -- suboptimal, e.g. in `ifThenElse True x y`, we will get back `x`, but
            -- with the annotation that was on the `ifThenElse` node. But we can't
            -- easily do better.
            -- See Note [Unserializable constants]
            Just t'
              | termIsSerializable binfo t'
              , matcherLikeBranchesAreValues binfo bn argCtx ->
                  x <$ t'
            _ -> t
    processTerm t = t

    -- Note [Conservative folding for matcher-like builtins]
    -- `evaluateBuiltins` may replace a builtin application with its result only when
    -- this preserves operational behaviour.
    -- Matcher-like builtins (e.g. `ifThenElse`) select one branch and discard others.
    -- Replacing the whole application with the selected branch is not conservative if
    -- a discarded branch is not already a value.
    -- So we only fold matcher-like builtins when all branches are values.
    -- See issue #6167.
    matcherLikeBranchesAreValues
      :: BuiltinsInfo uni fun
      -> fun
      -> AppContext tyname name uni fun a
      -> Bool
    matcherLikeBranchesAreValues info bn argCtx =
      case Map.lookup bn (info ^. biMatcherLike) of
        Nothing -> True
        -- Non-matcher-like builtins - do not discard branches
        Just (BuiltinMatcherLike splitPrism _) ->
          case preview splitPrism argCtx of
            Nothing -> False -- be conservative
            Just smc -> allBranchesAreValues smc
      where
        allBranchesAreValues =
          all isTermValueLike . extractTermAppArgs . smBranches

    -- Extract only term arguments from an application context, ignoring type arguments.
    extractTermAppArgs :: AppContext tyname name uni fun a -> [Term tyname name uni fun a]
    extractTermAppArgs = go []
      where
        go acc = \case
          TermAppContext arg _ ctx -> go (arg : acc) ctx
          TypeAppContext _ _ ctx -> go acc ctx
          AppContextEnd -> reverse acc

    -- A conservative PIR-side approximation of "already a value".
    -- Used only to decide whether it is safe to discard an unchosen branch
    -- of a matcher-like builtin during constant folding.
    isTermValueLike :: Term tyname name uni fun a -> Bool
    isTermValueLike = \case
      TyAbs {} -> True
      LamAbs {} -> True
      Constant {} -> True
      Constr _ _ _ xs -> all isTermValueLike xs
      IWrap _ _ _ t -> isTermValueLike t
      Var {} -> False
      Error {} -> False
      Let {} -> False
      Apply {} -> False
      TyInst {} -> False
      Unwrap {} -> False
      Builtin {} -> False
      Case {} -> False
