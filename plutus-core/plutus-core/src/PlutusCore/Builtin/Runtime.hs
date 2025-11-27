{-# LANGUAGE CPP        #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE StrictData #-}

module PlutusCore.Builtin.Runtime where

import PlutusPrelude

import PlutusCore.Builtin.KnownType
import PlutusCore.Evaluation.Machine.ExBudgetStream

import Control.DeepSeq
import Control.Monad.Except (throwError)
import NoThunks.Class

-- | A 'BuiltinRuntime' represents a possibly partial builtin application, including an empty
-- builtin application (i.e. just the builtin with no arguments).
--
-- Applying or type-instantiating a builtin peels off the corresponding constructor from its
-- 'BuiltinRuntime'.
--
-- 'BuiltinCostedResult' contains the cost (an 'ExBudgetStream') and the result (a
-- @BuiltinResult (HeadSpine val)@) of the builtin application. The cost is stored strictly, since
-- the evaluator is going to look at it and the result is stored lazily, since it's not supposed to
-- be forced before accounting for the cost of the application. If the cost exceeds the available
-- budget, the evaluator discards the result of the builtin application without ever forcing it and
-- terminates with evaluation failure. Allowing the user to compute something that they don't have
-- the budget for would be a major bug.
--
-- Evaluators that ignore the entire concept of costing (e.g. the CK machine) may of course force
-- the result of the builtin application unconditionally.
data BuiltinRuntime val
    = BuiltinCostedResult ExBudgetStream ~(BuiltinResult val)
    | BuiltinExpectArgument (val -> BuiltinRuntime val)
    | BuiltinExpectForce (BuiltinRuntime val)

instance NoThunks (BuiltinRuntime val) where
    wNoThunks ctx = \case
        -- Unreachable, because we don't allow nullary builtins and the 'BuiltinArrow' case only
        -- checks for WHNF without recursing. Hence we can throw if we reach this clause somehow.
        -- TODO: remove the CPP when rest of IOE moves to nothunks>=0.2
#if MIN_VERSION_nothunks(0,3,0)
        BuiltinCostedResult _ _    -> pure . Just $ ThunkInfo ctx Nothing
#elif MIN_VERSION_nothunks(0,2,0)
        BuiltinCostedResult _ _    -> pure . Just . ThunkInfo $ Left ctx
#else
        -- Plutus has moved to nothunks>=0.2, but some other IOE repos are using nothunks<0.2.
        -- As a consequence, cardano-constitution:create-json-envelope cannot be build.
        -- This is a workaround to make it build (default is buildable:False). See `cabal.project`
        BuiltinCostedResult _ _    -> pure . Just $ ThunkInfo ctx
#endif
        -- This one doesn't do much. It only checks that the function stored in the 'BuiltinArrow'
        -- is in WHNF. The function may contain thunks inside of it. Not sure if it's possible to do
        -- better, since the final 'BuiltinCostedResult' contains a thunk for the result of the
        -- builtin application anyway.
        BuiltinExpectArgument f    -> noThunks ctx f
        BuiltinExpectForce runtime -> noThunks ctx runtime

    showTypeOf = const "PlutusCore.Builtin.Runtime.BuiltinRuntime"

instance NFData (BuiltinRuntime val) where
    -- 'BuiltinRuntime' is strict (verified by the 'NoThunks' tests), hence we only need to force
    -- this to WHNF to get it forced to NF.
    rnf = rwhnf

{- Note [DO NOT newtype-wrap functions]
If you put a functional type into a @newtype@ rather than strict @data@, the GHC optimizer will be
able to see through it and will feel compelled to rearrange lambdas and case-expressions as it sees
fit, which it often does incorrectly due to @-fpedantic-bottoms@ not being enabled by default.

We've had a very confusing case of GHC turning

    case y of
        y' -> \x -> z

into

    \x -> case y of
        y' -> z

and ruining carefully set up optimizations
(see https://github.com/IntersectMBO/plutus/pull/4914#issuecomment-1396306606).

Even strict @data@ is slower than @newtype@, but in practice GHC is going to
worker-wrapper-transform such code making it as efficient as the @newtype@ version.

So you should never newtype-wrap functions, use strict @data@ instead.
-}

-- See Note [DO NOT newtype-wrap functions].
-- | A @data@ wrapper around a function returning the 'BuiltinRuntime' of a built-in function.
--
-- In order for lookups to be efficient the 'BuiltinRuntime's need to be cached, i.e. pulled out
-- of the function statically. See 'makeBuiltinMeaning' for how we achieve that.
data BuiltinsRuntime fun val = BuiltinsRuntime
    { unBuiltinsRuntime :: fun -> BuiltinRuntime val
    }

instance (Bounded fun, Enum fun) => NFData (BuiltinsRuntime fun val) where
    -- Force every 'BuiltinRuntime' stored in the environment.
    rnf (BuiltinsRuntime env) = foldr (\fun res -> env fun `seq` res) () enumerate

instance (Bounded fun, Enum fun) => NoThunks (BuiltinsRuntime fun val) where
    -- Ensure that every 'BuiltinRuntime' doesn't contain thunks after forcing it initially
    -- (we can't avoid the initial forcing, because we can't lookup the 'BuiltinRuntime' without
    -- forcing it, see https://stackoverflow.com/q/63441862).
    wNoThunks ctx (BuiltinsRuntime env) = allNoThunks $ map (wNoThunks ctx . env) enumerate
    showTypeOf = const "PlutusCore.Builtin.Runtime.BuiltinsRuntime"

builtinRuntimeFailure :: BuiltinError -> BuiltinRuntime val
builtinRuntimeFailure = BuiltinCostedResult (ExBudgetLast mempty) . throwError
-- See Note [INLINE and OPAQUE on error-related definitions].
{-# OPAQUE builtinRuntimeFailure #-}

-- | Look up the runtime info of a built-in function during evaluation.
lookupBuiltin :: fun -> BuiltinsRuntime fun val -> BuiltinRuntime val
lookupBuiltin fun (BuiltinsRuntime env) = env fun
{-# INLINE lookupBuiltin #-}
