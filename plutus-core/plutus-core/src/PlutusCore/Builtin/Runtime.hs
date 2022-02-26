{-# LANGUAGE RankNTypes     #-}
{-# LANGUAGE TypeFamilies   #-}

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
import PlutusCore.Evaluation.Machine.Exception

import Control.DeepSeq
import Control.Lens (ix, (^?))
import Control.Monad.Except
import Data.Array
import Data.Kind qualified as GHC (Type)
import GHC.Exts (inline)
import PlutusCore.Builtin.KnownType

import PlutusCore.Builtin.Emitter
import PlutusCore.Evaluation.Machine.ExBudget
import PlutusCore.Evaluation.Machine.ExMemory

data Nat = Z | S Nat

-- | Same as 'TypeScheme' except this one doesn't contain any evaluation-irrelevant types stuff.
data RuntimeScheme n where
    RuntimeSchemeResult :: RuntimeScheme 'Z
    RuntimeSchemeArrow :: RuntimeScheme n -> RuntimeScheme ('S n)
    RuntimeSchemeAll :: RuntimeScheme n -> RuntimeScheme n

type MakeKnownM = ExceptT (ErrorWithCause ReadKnownError ()) Emitter
type ReadKnownM = Either (ErrorWithCause ReadKnownError ())

type family ToDenotationType val (n :: Nat) :: GHC.Type where
    ToDenotationType val 'Z     = MakeKnownM val
    ToDenotationType val ('S n) = val -> ReadKnownM (ToDenotationType val n)

type family ToCostingType (n :: Nat) :: GHC.Type where
    ToCostingType 'Z     = ExBudget
    ToCostingType ('S n) = ExMemory -> ToCostingType n

-- we use strictdata, so this is just for the purpose of completeness
instance NFData (RuntimeScheme n) where
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
    forall n. BuiltinRuntime
        (RuntimeScheme n)
        ~(ToDenotationType val n)  -- Must be lazy, because we don't want to compute the denotation
                                   -- when it's fully saturated before figuring out what it's going
                                   -- to cost.
        ~(ToCostingType n)         -- We make this lazy, so that evaluators that don't care about
                                   -- costing can put @undefined@ here.
                                   -- TODO: we should test if making this strict introduces any
                                   -- measurable speedup.

instance NFData (BuiltinRuntime val) where
    rnf (BuiltinRuntime rs f exF) = rnf rs `seq` f `seq` rwhnf exF

-- | A 'BuiltinRuntime' for each builtin from a set of builtins.
newtype BuiltinsRuntime fun val = BuiltinsRuntime
    { unBuiltinRuntime :: Array fun (BuiltinRuntime val)
    }

deriving newtype instance (NFData fun) => NFData (BuiltinsRuntime fun val)

data UnliftMode
    = UnliftImmediately
    | UnliftWhenSaturated

unliftMode :: UnliftMode
unliftMode = UnliftImmediately

-- | Instantiate a 'BuiltinMeaning' given denotations of built-in functions and a cost model.
toBuiltinRuntime :: cost -> BuiltinMeaning val cost -> BuiltinRuntime val
toBuiltinRuntime cost (BuiltinMeaning sch f exF) =
    go sch $ \sch' toF' toExF' -> (BuiltinRuntime sch' $! (toF' $ pure f)) $! (toExF' $ exF cost) where
        go
            :: TypeScheme val args res
            -> (forall n.
                    RuntimeScheme n
                -> (ReadKnownM (FoldArgs args res) -> ToDenotationType val n)
                -> (FoldArgsEx args -> ToCostingType n)
                -> BuiltinRuntime val)
            -> BuiltinRuntime val
        go TypeSchemeResult       k =
            k
                RuntimeSchemeResult
                (\getRes -> liftEither getRes >>= makeKnown (Just ()))
                id
        go (TypeSchemeArrow schB) k =
            go schB $ \sch' toF' toExF' -> k
                (RuntimeSchemeArrow sch')
                (\getF x -> do
                    let getVal = readKnown (Just ()) x
                    case unliftMode of
                        UnliftImmediately   -> getVal <&> \val -> toF' (($ val) <$> getF)
                        UnliftWhenSaturated -> pure . toF' $ getF <*> getVal)
                (toExF' .)
        go (TypeSchemeAll _ schK) k = go schK $ k . RuntimeSchemeAll

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
