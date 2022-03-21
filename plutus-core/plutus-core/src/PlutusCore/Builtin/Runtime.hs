{-# LANGUAGE DataKinds      #-}
{-# LANGUAGE GADTs          #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators  #-}

{-# LANGUAGE StrictData     #-}

module PlutusCore.Builtin.Runtime where

import PlutusPrelude

import PlutusCore.Builtin.HasConstant
import PlutusCore.Builtin.Meaning
import PlutusCore.Builtin.TypeScheme
import PlutusCore.Core
import PlutusCore.Evaluation.Machine.Exception

import Control.DeepSeq
import Control.Lens (ix, (^?))
import Control.Monad.Except
import Data.Array
import Data.Kind qualified as GHC (Type)
import GHC.Exts (inline)
import PlutusCore.Builtin.KnownType

-- | Same as 'TypeScheme' except this one doesn't contain any evaluation-irrelevant types stuff.
data RuntimeScheme val (args :: [GHC.Type]) res where
    RuntimeSchemeResult
        :: KnownTypeIn (UniOf val) val res
        => RuntimeScheme val '[] res
    RuntimeSchemeArrow
        :: KnownTypeIn (UniOf val) val arg
        => RuntimeScheme val args res
        -> RuntimeScheme val (arg ': args) res
    RuntimeSchemeAll
        :: RuntimeScheme val args res
        -> RuntimeScheme val args res

-- we use strictdata, so this is just for the purpose of completeness
instance NFData (RuntimeScheme val args res) where
    rnf r = case r of
        RuntimeSchemeResult    -> rwhnf r
        RuntimeSchemeArrow arg -> rnf arg
        RuntimeSchemeAll arg   -> rnf arg

-- We tried instantiating 'BuiltinMeaning' on the fly and that was slower than precaching
-- 'BuiltinRuntime's.
-- | A 'BuiltinRuntime' represents a possibly partial builtin application.
-- We get an initial 'BuiltinRuntime' representing an empty builtin application (i.e. just the
-- builtin with no arguments) by instantiating (via 'toBuiltinRuntime') a 'BuiltinMeaning'.
--
-- A 'BuiltinRuntime' contains info that is used during evaluation:
--
-- 1. the 'TypeScheme' of the uninstantiated part of the builtin. I.e. initially it's the type
--      scheme of the whole builtin, but applying or type-instantiating the builtin peels off
--      the corresponding constructor from the type scheme
-- 2. the (possibly partially instantiated) denotation
-- 3. the (possibly partially instantiated) costing function
--
-- All the three are in sync in terms of partial instantiatedness due to 'TypeScheme' being a
-- GADT and 'FoldArgs' and 'FoldArgsEx' operating on the index of that GADT.
data BuiltinRuntime val =
    forall args res. BuiltinRuntime
        (RuntimeScheme val args res)
        ~(FoldArgs args res)  -- Must be lazy, because we don't want to compute the denotation when
                              -- it's fully saturated before figuring out what it's going to cost.
        ~(FoldArgsEx args)    -- We make this lazy, so that evaluators that don't care about costing
                              -- can put @undefined@ here. TODO: we should test if making this
                              -- strict introduces any measurable speedup.

instance NFData (BuiltinRuntime val) where
    rnf (BuiltinRuntime rs f exF) = rnf rs `seq` f `seq` rwhnf exF

-- | A 'BuiltinRuntime' for each builtin from a set of builtins.
newtype BuiltinsRuntime fun val = BuiltinsRuntime
    { unBuiltinRuntime :: Array fun (BuiltinRuntime val)
    }

deriving newtype instance (NFData fun) => NFData (BuiltinsRuntime fun val)

-- | Convert a 'TypeScheme' to a 'RuntimeScheme'.
typeSchemeToRuntimeScheme :: TypeScheme val args res -> RuntimeScheme val args res
typeSchemeToRuntimeScheme TypeSchemeResult       = RuntimeSchemeResult
typeSchemeToRuntimeScheme (TypeSchemeArrow schB) =
    RuntimeSchemeArrow $ typeSchemeToRuntimeScheme schB
typeSchemeToRuntimeScheme (TypeSchemeAll _ schK) =
    RuntimeSchemeAll $ typeSchemeToRuntimeScheme schK

-- | Instantiate a 'BuiltinMeaning' given denotations of built-in functions and a cost model.
toBuiltinRuntime :: cost -> BuiltinMeaning val cost -> BuiltinRuntime val
toBuiltinRuntime cost (BuiltinMeaning sch f exF) =
    BuiltinRuntime (typeSchemeToRuntimeScheme sch) f (exF cost)

-- See Note [Inlining meanings of builtins].
-- | Calculate runtime info for all built-in functions given denotations of builtins
-- and a cost model.
toBuiltinsRuntime
    :: (cost ~ CostingPart uni fun, HasConstantIn uni val, ToBuiltinMeaning uni fun)
    => cost -> BuiltinsRuntime fun val
toBuiltinsRuntime cost =
    BuiltinsRuntime . tabulateArray $ toBuiltinRuntime cost . inline toBuiltinMeaning
{-# INLINE toBuiltinsRuntime #-}

-- | Look up the runtime info of a built-in function during evaluation.
lookupBuiltin
    :: (MonadError (ErrorWithCause err cause) m, AsMachineError err fun, Ix fun)
    => fun -> BuiltinsRuntime fun val -> m (BuiltinRuntime val)
-- @Data.Array@ doesn't seem to have a safe version of @(!)@, hence we use a prism.
lookupBuiltin fun (BuiltinsRuntime env) = case env ^? ix fun of
    Nothing  -> throwingWithCause _MachineError (UnknownBuiltin fun) Nothing
    Just bri -> pure bri
