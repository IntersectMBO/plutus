{-# LANGUAGE GADTs #-}

module PlutusCore.Builtin.Runtime where

import PlutusPrelude

import PlutusCore.Builtin.HasConstant
import PlutusCore.Builtin.Meaning
import PlutusCore.Builtin.TypeScheme
import PlutusCore.Evaluation.Machine.Exception

import Control.Lens (ix, (^?))
import Control.Monad.Except
import Data.Array

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
        (TypeScheme val args res)
        (FoldArgs args res)  -- Must be lazy, because we don't want to compute the denotation when
                             -- it's fully saturated before figuring out what it's going to cost.
        (FoldArgsEx args)    -- We make this lazy, so that evaluators that don't care about costing
                             -- can put @undefined@ here. TODO: we should test if making this strict
                             -- introduces any measurable speedup.

-- | A 'BuiltinRuntime' for each builtin from a set of builtins.
newtype BuiltinsRuntime fun val = BuiltinsRuntime
    { unBuiltinRuntime :: Array fun (BuiltinRuntime val)
    }

-- | Instantiate a 'BuiltinMeaning' given denotations of built-in functions and a cost model.
toBuiltinRuntime :: cost -> BuiltinMeaning val cost -> BuiltinRuntime val
toBuiltinRuntime cost (BuiltinMeaning sch f exF) = BuiltinRuntime sch f (exF cost)

-- | Calculate runtime info for all built-in functions given denotations of builtins
-- and a cost model.
toBuiltinsRuntime
    :: (cost ~ CostingPart uni fun, HasConstantIn uni val, ToBuiltinMeaning uni fun)
    => cost -> BuiltinsRuntime fun val
toBuiltinsRuntime cost =
    BuiltinsRuntime . tabulateArray $ toBuiltinRuntime cost . toBuiltinMeaning

-- | Look up the runtime info of a built-in function during evaluation.
lookupBuiltin
    :: (MonadError (ErrorWithCause err cause) m, AsMachineError err fun, Ix fun)
    => fun -> BuiltinsRuntime fun val -> m (BuiltinRuntime val)
-- @Data.Array@ doesn't seem to have a safe version of @(!)@, hence we use a prism.
lookupBuiltin fun (BuiltinsRuntime env) = case env ^? ix fun of
    Nothing  -> throwingWithCause _MachineError (UnknownBuiltin fun) Nothing
    Just bri -> pure bri
