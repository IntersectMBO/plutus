{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DefaultSignatures     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE TypeOperators         #-}

{-# LANGUAGE StrictData            #-}

module PlutusCore.Builtin.Runtime where

import PlutusPrelude

import PlutusCore.Builtin.HasConstant
import PlutusCore.Builtin.KnownType
import PlutusCore.Builtin.Meaning
import PlutusCore.Builtin.TypeScheme
import PlutusCore.Core
import PlutusCore.Evaluation.Machine.Exception

import Control.Lens (ix, (^?))
import Control.Monad.Except
import Data.Array
import Data.Kind qualified as GHC (Type)
import GHC.Exts (inline)

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

-- | A 'BuiltinRuntime' for each builtin from a set of builtins.
newtype BuiltinsRuntime fun val = BuiltinsRuntime
    { unBuiltinRuntime :: Array fun (BuiltinRuntime val)
    }

-- | Convert a 'TypeScheme' to a 'RuntimeScheme'.
typeSchemeToRuntimeScheme :: TypeScheme val args res -> RuntimeScheme val args res
typeSchemeToRuntimeScheme TypeSchemeResult = RuntimeSchemeResult
typeSchemeToRuntimeScheme (TypeSchemeArrow schB) =
    RuntimeSchemeArrow $ typeSchemeToRuntimeScheme schB
typeSchemeToRuntimeScheme (TypeSchemeAll _ schK) =
    RuntimeSchemeAll $ typeSchemeToRuntimeScheme schK

-- | Instantiate a 'BuiltinMeaning' given denotations of built-in functions and a cost model.
toBuiltinRuntime :: cost -> BuiltinMeaning val cost -> BuiltinRuntime val
toBuiltinRuntime cost (BuiltinMeaning sch f exF) =
    BuiltinRuntime (typeSchemeToRuntimeScheme sch) f (exF cost)

-- | This is a function turned into a class for the sake of specialization and inspection.
-- Every instance of this class MUST use the default implementation of 'toBuiltinsRuntime',
-- i.e. not define 'toBuiltinsRuntime' at all. Having this class allows us to inline away lots of
-- abstractions used by the builtins machinery.
--
-- For performance-critical code both @fun@ and @val@ need to be specified as concrete data types
-- for inlining to happen. In other places it's fine to only specify one of them.
class ToBuiltinsRuntime fun val where
    -- Somehow getting rid of the @uni ~ UniOf val@ constraint by substituting @UniOf val@ for @uni@
    -- completely breaks inlining of 'toBuiltinMeaning'.
    -- | Calculate runtime info for all built-in functions given a cost model.
    toBuiltinsRuntime :: uni ~ UniOf val => CostingPart uni fun -> BuiltinsRuntime fun val
    default toBuiltinsRuntime
        :: (HasConstantIn uni val, ToBuiltinMeaning uni fun)
        => CostingPart uni fun -> BuiltinsRuntime fun val
    -- Do we want to mark this as @INLINE@? Or @NOINLINE@? The former has the advantage of allowing
    -- us to optimize some of the @cost@-related operations away at the cost of potentially blowing
    -- up compilation times or even the size of the executable (probably not though). The latter is
    -- the opposite. Currently we let GHC decide: it won't inline 'toBuiltinsRuntime' if it's huge.
    toBuiltinsRuntime cost =
        -- 'toBuiltinMeaning' can be a huge function, hence an explicit 'inline'.
        BuiltinsRuntime . tabulateArray $ toBuiltinRuntime cost . inline toBuiltinMeaning

-- | Look up the runtime info of a built-in function during evaluation.
lookupBuiltin
    :: (MonadError (ErrorWithCause err cause) m, AsMachineError err fun, Ix fun)
    => fun -> BuiltinsRuntime fun val -> m (BuiltinRuntime val)
-- @Data.Array@ doesn't seem to have a safe version of @(!)@, hence we use a prism.
lookupBuiltin fun (BuiltinsRuntime env) = case env ^? ix fun of
    Nothing  -> throwingWithCause _MachineError (UnknownBuiltin fun) Nothing
    Just bri -> pure bri
