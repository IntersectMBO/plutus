{-# LANGUAGE AllowAmbiguousTypes       #-}
{-# LANGUAGE ConstraintKinds           #-}
{-# LANGUAGE DataKinds                 #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE PolyKinds                 #-}
{-# LANGUAGE StandaloneKindSignatures  #-}
{-# LANGUAGE TypeApplications          #-}
{-# LANGUAGE TypeFamilies              #-}
{-# LANGUAGE TypeOperators             #-}
{-# LANGUAGE UndecidableInstances      #-}

{-# LANGUAGE StrictData                #-}

module PlutusCore.Builtin.Meaning where

import PlutusPrelude

import PlutusCore.Builtin.Elaborate
import PlutusCore.Builtin.HasConstant
import PlutusCore.Builtin.KnownKind
import PlutusCore.Builtin.KnownType
import PlutusCore.Builtin.KnownTypeAst
import PlutusCore.Builtin.Runtime
import PlutusCore.Builtin.TypeScheme
import PlutusCore.Core
import PlutusCore.Name

import Data.Array
import Data.Kind qualified as GHC
import Data.Proxy
import Data.Some.GADT
import GHC.Exts (inline)
import GHC.TypeLits

-- | Turn a list of Haskell types @args@ into a functional type ending in @res@.
--
-- >>> :set -XDataKinds
-- >>> :kind! FoldArgs [(), Bool] Integer
-- FoldArgs [(), Bool] Integer :: *
-- = () -> Bool -> Integer
type family FoldArgs args res where
    FoldArgs '[]           res = res
    FoldArgs (arg ': args) res = arg -> FoldArgs args res

-- | The meaning of a built-in function consists of its type represented as a 'TypeScheme',
-- its Haskell denotation and a costing function (both in uninstantiated form).
--
-- The 'TypeScheme' of a built-in function is used for
--
-- 1. computing the PLC type of the function to be used during type checking
-- 2. checking equality of the expected type of an argument of a builtin and the actual one
--    during evaluation, so that we can avoid unsafe-coercing
--
-- A costing function for a built-in function is computed from a cost model for all built-in
-- functions from a certain set, hence the @cost@ parameter.
--
-- The denotation is lazy, so that we don't need to worry about a builtin being bottom
-- (happens in tests). The production path is not affected by that, since only runtime denotations
-- are used for evaluation.
data BuiltinMeaning val cost =
    forall args res. BuiltinMeaning
        (TypeScheme val args res)
        ~(FoldArgs args res)
        (BuiltinRuntimeOptions (Length args) val cost)

-- | Constraints available when defining a built-in function.
type HasMeaningIn uni val = (Typeable val, HasConstantIn uni val)

-- | A type class for \"each function from a set of built-in functions has a 'BuiltinMeaning'\".
class (Typeable uni, Typeable fun, Bounded fun, Enum fun, Ix fun) => ToBuiltinMeaning uni fun where
    -- | The @cost@ part of 'BuiltinMeaning'.
    type CostingPart uni fun

    -- | Get the 'BuiltinMeaning' of a built-in function.
    toBuiltinMeaning :: HasMeaningIn uni val => fun -> BuiltinMeaning val (CostingPart uni fun)

-- | Get the type of a built-in function.
typeOfBuiltinFunction :: forall uni fun. ToBuiltinMeaning uni fun => fun -> Type TyName uni ()
typeOfBuiltinFunction fun = case toBuiltinMeaning @_ @_ @(Term TyName Name uni fun ()) fun of
    BuiltinMeaning sch _ _ -> typeSchemeToType sch

{- Note [Automatic derivation of type schemes]
We use two type classes for automatic derivation of type/runtime schemes and runtime denotations:
'KnownPolytype' and 'KnownMonotype'.
The terminology is due to https://en.wikipedia.org/wiki/Hindley%E2%80%93Milner_type_system#The_Hindley%E2%80%93Milner_type_system

Check out the source of "PlutusCore.Builtin.Runtime" for an explanation of what a runtime
denotation is.

'KnownPolytype' and 'KnownMonotype' are responsible for deriving polymorphic and monomorphic types,
respectively.

'KnownPolytype' turns every bound variable into a 'TypeSchemeAll'/'RuntimeSchemeAll'. We extract
variables from the type of the Haskell denotation using the 'ToBinds' associated type
family. Variables are collected in the order that they appear in (i.e. just like in Haskell). For
example, processing a type like

      :: ( a ~ Opaque val (TyVarRep ('TyNameRep "a" 0))
         , b ~ Opaque val (TyVarRep ('TyNameRep "b" 1))
         )
      => b -> a -> b

with 'ToBinds' results in the following list of bindings:

    '[ 'Some ('TyNameRep "b" 1), 'Some ('TyNameRep "a" 0) ]

'KnownMonotype' turns every argument that the Haskell denotation of a builtin receives into a
'TypeSchemeArrow'/'RuntimeSchemeArrow'. We extract the arguments from the type of the Haskell
denotation using the 'GetArgs' type family.

Higher-kinded type variables are fully supported.

At this point in the pipeline the type of the denotation of a builtin is assumed to be fully
elaborated (i.e. monomorphic).
-}

-- | Compute the length of a type-level list.
type Length :: forall a. [a] -> Peano
type family Length xs where
    Length '[]       = 'Z
    Length (_ ': xs) = 'S (Length xs)

-- | Chop a function type to get a list of its argument types.
type GetArgs :: GHC.Type -> [GHC.Type]
type family GetArgs a where
    GetArgs (a -> b) = a ': GetArgs b
    GetArgs _        = '[]

-- | A class that allows us to derive a monotype for a builtin.
-- We could've easily computed a 'RuntimeScheme' from a 'TypeScheme' but not statically (due to
-- unfolding not working for recursive functions and 'TypeScheme' being recursive, i.e. requiring
-- the conversion function to be recursive), and so it would cause us to retain a lot of
-- evaluation-irrelevant stuff in the constructors of 'TypeScheme', which makes it much harder to
-- read the Core. Technically speaking, we could convert a 'TypeScheme' to a 'RuntimeScheme'
-- statically if we changed the definition of 'TypeScheme' and made it a singleton, but then the
-- conversion function would have to become a class anyway and we'd just replicate what we have
-- here, except in a much more complicated way. It's also more efficient to generate
-- 'RuntimeScheme's directly, but that shouldn't really matter, given that they are only computed
-- once and get cached afterwards.
--
-- Similarly, we could've computed the runtime denotations ('toImmediateF' and 'toDeferredF')
-- from a 'TypeScheme' but not statically again, and that would break inlining and basically all
-- the optimization.
class KnownMonotype val args res where
    knownMonotype :: TypeScheme val args res
    knownMonoruntime :: RuntimeScheme (Length args)

    -- | Convert the denotation of a builtin to its runtime counterpart with immediate unlifting.
    toImmediateF :: FoldArgs args res -> ToRuntimeDenotationType val (Length args)

    -- | Convert the denotation of a builtin to its runtime counterpart with deferred unlifting.
    -- The argument is in 'ReadKnownM', because that's what deferred unlifting amounts to:
    -- passing the action returning the builtin application around until full saturation, which is
    -- when the action actually gets run.
    toDeferredF :: ReadKnownM (FoldArgs args res) -> ToRuntimeDenotationType val (Length args)

-- | Once we've run out of term-level arguments, we return a
-- 'TypeSchemeResult'/'RuntimeSchemeResult'.
instance (Typeable res, KnownTypeAst (UniOf val) res, MakeKnown val res) =>
            KnownMonotype val '[] res where
    knownMonotype = TypeSchemeResult
    knownMonoruntime = RuntimeSchemeResult

    toImmediateF = makeKnown
    {-# INLINE toImmediateF #-}

    -- For deferred unlifting we need to lift the 'ReadKnownM' action into 'MakeKnownM',
    -- hence 'liftReadKnownM'.
    toDeferredF getRes = liftReadKnownM getRes >>= makeKnown
    {-# INLINE toDeferredF #-}

-- | Every term-level argument becomes a 'TypeSchemeArrow'/'RuntimeSchemeArrow'.
instance
        ( Typeable arg, KnownTypeAst (UniOf val) arg, MakeKnown val arg, ReadKnown val arg
        , KnownMonotype val args res
        ) => KnownMonotype val (arg ': args) res where
    knownMonotype = TypeSchemeArrow knownMonotype
    knownMonoruntime = RuntimeSchemeArrow $ knownMonoruntime @val @args @res

    -- Unlift, then recurse.
    toImmediateF f = fmap (toImmediateF @val @args @res . f) . readKnown
    {-# INLINE toImmediateF #-}

    -- Grow the builtin application within the received action and recurse on the result.
    toDeferredF getF = \arg ->
        -- The bang is very important: without it GHC thinks that the argument may not be needed in
        -- the end and so creates a thunk for it, which is not only unnecessary allocation, but also
        -- prevents things from being unboxed. So ironically computing the unlifted value strictly
        -- is the best way of doing deferred unlifting. All this means that while the resulting
        -- 'Either' is only handled upon full saturation and any evaluation failure is only
        -- registered when the whole builtin application is evaluated, a Haskell exception will
        -- occur the same way as with immediate unlifting. It shouldn't matter though, because a
        -- builtin is not supposed to throw an exception at any stage, that would be a bug
        -- regardless of how unlifting is aligned.
        --
        -- 'pure' signifies that no failure can occur at this point.
        pure . toDeferredF @val @args @res $! getF <*> readKnown arg
    {-# INLINE toDeferredF #-}

-- | A class that allows us to derive a polytype for a builtin.
class KnownMonotype val args res => KnownPolytype (binds :: [Some TyNameRep]) val args res where
    knownPolytype :: TypeScheme val args res
    knownPolyruntime :: RuntimeScheme (Length args)

-- | Once we've run out of type-level arguments, we start handling term-level ones.
instance KnownMonotype val args res => KnownPolytype '[] val args res where
    knownPolytype = knownMonotype
    knownPolyruntime = knownMonoruntime @val @args @res

-- Here we unpack an existentially packed @kind@ and constrain it afterwards!
-- So promoted existentials are true sigmas! If we were at the term level, we'd have to pack
-- @kind@ along with the @KnownKind kind@ constraint, otherwise when we unpack the existential,
-- all information is lost and we can't do anything with @kind@.
-- | Every type-level argument becomes a 'TypeSchemeAll'.
instance (KnownSymbol name, KnownNat uniq, KnownKind kind, KnownPolytype binds val args res) =>
            KnownPolytype ('Some ('TyNameRep @kind name uniq) ': binds) val args res where
    knownPolytype = TypeSchemeAll @name @uniq @kind Proxy $ knownPolytype @binds
    knownPolyruntime = RuntimeSchemeAll $ knownPolyruntime @binds @val @args @res

-- | Ensure a built-in function is not nullary and throw a nice error otherwise.
type ThrowOnBothEmpty :: [Some TyNameRep] -> [GHC.Type] -> Bool -> GHC.Type -> GHC.Constraint
type family ThrowOnBothEmpty binds args isBuiltin a where
    ThrowOnBothEmpty '[] '[] 'True a =
        TypeError (
            'Text "A built-in function must take at least one type or term argument" ':$$:
            'Text "‘" ':<>: 'ShowType a ':<>: 'Text "’ is a built-in type" ':<>:
            'Text " so you can embed any of its values as a constant" ':$$:
            'Text "If you still want a built-in function, add a dummy ‘()’ argument"
            )
    ThrowOnBothEmpty '[] '[] 'False a =
        TypeError (
            'Text "A built-in function must take at least one type or term argument" ':$$:
            'Text "To fix this error add a dummy ‘()’ argument"
            )
    ThrowOnBothEmpty _ _ _ _ = ()

-- | A function turned into a type class with exactly one fully general instance.
-- We can't package up the constraints of 'makeBuiltinMeaning' (see the instance) into a type or
-- class synonym, because they contain a bunch of variables defined by @~@ or determined via
-- functional dependencies and neither class nor type definitions can handle that
-- (see https://gitlab.haskell.org/ghc/ghc/-/issues/7100). Inlining three lines of constraints
-- whenever we need to call 'makeBuiltinMeaning' over a non-concrete type is a bad option and this
-- abstraction is free anyway, hence its existence.
--
-- The @a@ type variable goes first, because @makeBuiltinMeaning \@A@ is a common pattern.
class MakeBuiltinMeaning a val where
    -- See Note [Automatic derivation of type schemes]
    -- | Construct the meaning for a built-in function by automatically deriving its
    -- 'TypeScheme', given
    --
    -- 1. the denotation of the builtin
    -- 2. an uninstantiated costing function
    makeBuiltinMeaning
        :: a -> (cost -> ToCostingType (Length (GetArgs a))) -> BuiltinMeaning val cost
instance
        ( binds ~ ToBinds a, args ~ GetArgs a, a ~ FoldArgs args res
        , ThrowOnBothEmpty binds args (IsBuiltin a) a
        , ElaborateFromTo 0 j val a, KnownPolytype binds val args res
        ) => MakeBuiltinMeaning a val where
    makeBuiltinMeaning f toExF =
        BuiltinMeaning (knownPolytype @binds @val @args @res) f $
            BuiltinRuntimeOptions
                { _broRuntimeScheme = knownPolyruntime @binds @val @args @res
                , _broImmediateF    = toImmediateF @val @args @res f
                , _broDeferredF     = toDeferredF @val @args @res $ pure f
                , _broToExF         = toExF
                }
    {-# INLINE makeBuiltinMeaning #-}

-- | Convert a 'BuiltinMeaning' to a 'BuiltinRuntime' given an 'UnliftingMode' and a cost model.
toBuiltinRuntime :: UnliftingMode -> cost -> BuiltinMeaning val cost -> BuiltinRuntime val
toBuiltinRuntime unlMode cost (BuiltinMeaning _ _ runtimeOpts) =
    fromBuiltinRuntimeOptions unlMode cost runtimeOpts
{-# INLINE toBuiltinRuntime #-}

-- See Note [Inlining meanings of builtins].
-- | Calculate runtime info for all built-in functions given denotations of builtins,
-- an 'UnliftingMode' and a cost model.
toBuiltinsRuntime
    :: (cost ~ CostingPart uni fun, ToBuiltinMeaning uni fun, HasMeaningIn uni val)
    => UnliftingMode -> cost -> BuiltinsRuntime fun val
toBuiltinsRuntime unlMode cost =
    let arr = tabulateArray $ toBuiltinRuntime unlMode cost . inline toBuiltinMeaning
     in -- Force array elements to WHNF
        case foldr seq () arr of () -> BuiltinsRuntime arr
{-# INLINE toBuiltinsRuntime #-}
