{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}

{-# LANGUAGE StrictData #-}

module PlutusCore.Builtin.Runtime where

import PlutusCore.Builtin.KnownType
import PlutusCore.Evaluation.Machine.ExBudget
import PlutusCore.Evaluation.Machine.Exception

import Control.DeepSeq
import Control.Lens (ix, (^?))
import Control.Monad.Except
import Data.Array
import NoThunks.Class

-- We tried instantiating 'BuiltinMeaning' on the fly and that was slower than precaching
-- 'BuiltinRuntime's.
-- | A 'BuiltinRuntime' represents a possibly partial builtin application.
-- We get an initial 'BuiltinRuntime' representing an empty builtin application (i.e. just the
-- builtin with no arguments) by instantiating (via 'fromBuiltinRuntimeOptions') a
-- 'BuiltinRuntimeOptions'.
--
-- A 'BuiltinRuntime' contains info that is used during evaluation:
--
-- 1. the 'RuntimeScheme' of the uninstantiated part of the builtin. I.e. initially it's the runtime
--      scheme of the whole builtin, but applying or type-instantiating the builtin peels off
--      the corresponding constructor from the runtime scheme
-- 2. the (possibly partially instantiated) runtime denotation
-- 3. the (possibly partially instantiated) costing function
--
-- All the three are in sync in terms of partial instantiatedness due to 'RuntimeScheme' being a
-- GADT and 'ToRuntimeDenotationType' and 'ToCostingType' operating on the index of that GADT.
data BuiltinRuntime fun val
    = BuiltinResult fun ExBudget ~(MakeKnownM val)
    | BuiltinArrow (val -> ReadKnownM (BuiltinRuntime fun val))
    | BuiltinAll (BuiltinRuntime fun val)

instance NoThunks (BuiltinRuntime fun val) where
    wNoThunks ctx = \case
        -- Unreachable, because we don't allow nullary builtins and the 'BuiltinArrow' case only
        -- checks for WHNF without recursing. Hence we can throw if we reach this clause somehow.
        BuiltinResult _ _ _ -> pure . Just $ ThunkInfo ctx
        BuiltinArrow f      -> noThunks ctx f
        BuiltinAll runtime  -> noThunks ctx runtime

    showTypeOf = const "PlutusCore.Builtin.Runtime.BuiltinRuntime"

-- | Determines how to unlift arguments. The difference is that with 'UnliftingImmediate' unlifting
-- is performed immediately after a builtin gets the argument and so can fail immediately too, while
-- with deferred unlifting all arguments are unlifted upon full saturation, hence no failure can
-- occur until that. The former makes it much harder to specify the behaviour of builtins and
-- so 'UnliftingDeferred' is the preferred mode.
data UnliftingMode
    = UnliftingImmediate
    | UnliftingDeferred

-- | A 'BuiltinRuntimeOptions' is a precursor to 'BuiltinRuntime'. One gets the latter from the
-- former by choosing the runtime denotation of the builtin (either '_broImmediateF' for immediate
-- unlifting or '_broDeferredF' for deferred unlifting, see 'UnliftingMode' for details) and by
-- instantiating '_broToExF' with a cost model to get the costing function for the builtin.
--
-- The runtime denotations are lazy, so that we don't need to worry about a builtin being bottom
-- (happens in tests). The production path is not affected by that, since 'BuiltinRuntimeOptions'
-- doesn't survive optimization.
data BuiltinRuntimeOptions val cost = BuiltinRuntimeOptions
    { _broImmediateF :: forall fun. fun -> cost -> BuiltinRuntime fun val
    , _broDeferredF  :: forall fun. fun -> cost -> BuiltinRuntime fun val
    }

-- | Convert a 'BuiltinRuntimeOptions' to a 'BuiltinRuntime' given an 'UnliftingMode' and a cost
-- model.
fromBuiltinRuntimeOptions
    :: UnliftingMode -> fun -> cost -> BuiltinRuntimeOptions val cost -> BuiltinRuntime fun val
fromBuiltinRuntimeOptions unlMode fun cost (BuiltinRuntimeOptions immF defF) =
    case unlMode of
        UnliftingImmediate -> immF fun cost
        UnliftingDeferred  -> defF fun cost
{-# INLINE fromBuiltinRuntimeOptions #-}

instance NFData (BuiltinRuntime fun val) where
    rnf = rwhnf

-- | A 'BuiltinRuntime' for each builtin from a set of builtins.
newtype BuiltinsRuntime fun val = BuiltinsRuntime
    { unBuiltinRuntime :: Array fun (BuiltinRuntime fun val)
    }

deriving newtype instance (NFData fun) => NFData (BuiltinsRuntime fun val)

instance NoThunks (BuiltinsRuntime fun val) where
    wNoThunks ctx (BuiltinsRuntime arr) = allNoThunks (noThunks ctx <$> elems arr)
    showTypeOf = const "PlutusCore.Builtin.Runtime.BuiltinsRuntime"

-- | Look up the runtime info of a built-in function during evaluation.
lookupBuiltin
    :: (MonadError (ErrorWithCause err cause) m, AsMachineError err fun, Ix fun)
    => fun -> BuiltinsRuntime fun val -> m (BuiltinRuntime fun val)
-- @Data.Array@ doesn't seem to have a safe version of @(!)@, hence we use a prism.
lookupBuiltin fun (BuiltinsRuntime env) = case env ^? ix fun of
    Nothing  -> throwingWithCause _MachineError (UnknownBuiltin fun) Nothing
    Just bri -> pure bri
