{-# LANGUAGE DataKinds                #-}
{-# LANGUAGE GADTs                    #-}
{-# LANGUAGE LambdaCase               #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeFamilies             #-}
{-# LANGUAGE TypeOperators            #-}

{-# LANGUAGE StrictData               #-}

module PlutusCore.Builtin.Runtime where

import PlutusPrelude

import PlutusCore.Builtin.KnownType
import PlutusCore.Evaluation.Machine.ExBudget
import PlutusCore.Evaluation.Machine.ExMemory
import PlutusCore.Evaluation.Machine.Exception

import Control.DeepSeq
import Control.Lens (ix, (^?))
import Control.Monad.Except
import Data.Array
import Data.Kind qualified as GHC (Type)
import NoThunks.Class as NoThunks

-- | Peano numbers. Normally called @Nat@, but that is already reserved by @base@.
data Peano
    = Z
    | S Peano

-- | Same as 'TypeScheme' except this one doesn't contain any evaluation-irrelevant types stuff.
-- @n@ represents the number of term-level arguments that a builtin takes.
data RuntimeScheme n where
    RuntimeSchemeResult :: RuntimeScheme 'Z
    RuntimeSchemeArrow  :: RuntimeScheme n -> RuntimeScheme ('S n)
    RuntimeSchemeAll    :: RuntimeScheme n -> RuntimeScheme n

deriving stock instance Eq   (RuntimeScheme n)
deriving stock instance Show (RuntimeScheme n)

-- we use strictdata, so this is just for the purpose of completeness
instance NFData (RuntimeScheme n) where
    rnf r = case r of
        RuntimeSchemeResult    -> rwhnf r
        RuntimeSchemeArrow arg -> rnf arg
        RuntimeSchemeAll arg   -> rnf arg

instance NoThunks (RuntimeScheme n) where
    wNoThunks ctx = \case
        RuntimeSchemeResult  -> pure Nothing
        RuntimeSchemeArrow s -> noThunks ctx s
        RuntimeSchemeAll s   -> noThunks ctx s
    showTypeOf = const "PlutusCore.Builtin.Runtime.RuntimeScheme"

-- | Compute the runtime denotation type of a builtin given the type of values and the number of
-- arguments that the builtin takes. A \"runtime denotation type\" is different from a regular
-- denotation type in that a regular one can have any 'ReadKnownIn' type as an argument and can
-- return any 'MakeKnownIn' type, while in a runtime one only @val@ can appear as the type of an
-- argument, as well as in the result type. This is what we get by calling 'readKnown' over each
-- argument of the denotation and calling 'makeKnown' over its result.
type ToRuntimeDenotationType :: GHC.Type -> Peano -> GHC.Type
type family ToRuntimeDenotationType val n where
    ToRuntimeDenotationType val 'Z     = MakeKnownM () val
    -- 'ReadKnownM' is required here only for immediate unlifting, because deferred unlifting
    -- doesn't need the ability to fail in the middle of a builtin application, but having a uniform
    -- interface for both the ways of doing unlifting is way too convenient, hence we decided to pay
    -- the price (about 1-2% of total evaluation time) for now.
    ToRuntimeDenotationType val ('S n) = val -> ReadKnownM () (ToRuntimeDenotationType val n)

-- | Compute the costing type for a builtin given the number of arguments that the builtin takes.
type ToCostingType :: Peano -> GHC.Type
type family ToCostingType n where
    ToCostingType 'Z     = ExBudget
    ToCostingType ('S n) = ExMemory -> ToCostingType n

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
data BuiltinRuntime val =
    forall n. BuiltinRuntime
        (RuntimeScheme n)
        ~(ToRuntimeDenotationType val n)  -- Must be lazy, because we don't want to compute the
                                          -- denotation when it's fully saturated before figuring
                                          -- out what it's going to cost.
        (ToCostingType n)

instance NoThunks (BuiltinRuntime val) where
    -- Skipping `_denot` in `allNoThunks` check, since it is supposed to be lazy and
    -- is allowed to contain thunks.
    wNoThunks ctx (BuiltinRuntime sch _denot costing) =
        allNoThunks
            [ -- The order here is important: we must first check that `sch` doesn't have
              -- thunks, before inspecting it in `noThunksInCosting`.
              noThunks ctx sch
            , noThunksInCosting ctx costing sch
            ]

    showTypeOf = const "PlutusCore.Builtin.Runtime.BuiltinRuntime"

-- | Check whether the given `ToCostingType n` contains thunks. The `RuntimeScheme n` is used to
-- refine `n`.
noThunksInCosting :: NoThunks.Context -> ToCostingType n -> RuntimeScheme n -> IO (Maybe ThunkInfo)
noThunksInCosting ctx costing = \case
    -- @n ~ 'Z@, and @ToCostingType n ~ ExBudget@, which should not be a thunk or contain
    -- nested thunks.
    RuntimeSchemeResult ->
        noThunks ctx costing
    RuntimeSchemeArrow _ ->
        noThunks ctx costing
    RuntimeSchemeAll sch ->
        noThunksInCosting ctx costing sch

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
data BuiltinRuntimeOptions n val cost = BuiltinRuntimeOptions
    { _broRuntimeScheme :: RuntimeScheme n
    , _broImmediateF    :: ToRuntimeDenotationType val n
    , _broDeferredF     :: ToRuntimeDenotationType val n
    , _broToExF         :: cost -> ToCostingType n
    }

-- | Convert a 'BuiltinRuntimeOptions' to a 'BuiltinRuntime' given an 'UnliftingMode' and a cost
-- model.
fromBuiltinRuntimeOptions
    :: UnliftingMode -> cost -> BuiltinRuntimeOptions n val cost -> BuiltinRuntime val
fromBuiltinRuntimeOptions unlMode cost (BuiltinRuntimeOptions sch immF defF toExF) =
    BuiltinRuntime sch f $ toExF cost where
        f = case unlMode of
                UnliftingImmediate -> immF
                UnliftingDeferred  -> defF
{-# INLINE fromBuiltinRuntimeOptions #-}

instance NFData (BuiltinRuntime val) where
    rnf (BuiltinRuntime rs f exF) = rnf rs `seq` f `seq` rwhnf exF

-- | A 'BuiltinRuntime' for each builtin from a set of builtins.
newtype BuiltinsRuntime fun val = BuiltinsRuntime
    { unBuiltinRuntime :: Array fun (BuiltinRuntime val)
    }

deriving newtype instance (NFData fun) => NFData (BuiltinsRuntime fun val)

instance NoThunks (BuiltinsRuntime fun val) where
    wNoThunks ctx (BuiltinsRuntime arr) = allNoThunks (noThunks ctx <$> elems arr)
    showTypeOf = const "PlutusCore.Builtin.Runtime.BuiltinsRuntime"

-- | Look up the runtime info of a built-in function during evaluation.
lookupBuiltin
    :: (MonadError (ErrorWithCause err cause) m, AsMachineError err fun, Ix fun)
    => fun -> BuiltinsRuntime fun val -> m (BuiltinRuntime val)
-- @Data.Array@ doesn't seem to have a safe version of @(!)@, hence we use a prism.
lookupBuiltin fun (BuiltinsRuntime env) = case env ^? ix fun of
    Nothing  -> throwingWithCause _MachineError (UnknownBuiltin fun) Nothing
    Just bri -> pure bri
