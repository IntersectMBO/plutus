-- GHC doesn't like the definition of 'makeBuiltinMeaning'.
{-# OPTIONS_GHC -fno-warn-redundant-constraints #-}

{-# LANGUAGE AllowAmbiguousTypes       #-}
{-# LANGUAGE DataKinds                 #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE FunctionalDependencies    #-}
{-# LANGUAGE PolyKinds                 #-}
{-# LANGUAGE StandaloneKindSignatures  #-}
{-# LANGUAGE TypeApplications          #-}
{-# LANGUAGE TypeFamilies              #-}
{-# LANGUAGE TypeOperators             #-}
{-# LANGUAGE UndecidableInstances      #-}

-- DO NOT enable @StrictData@ in this file as it makes the evaluator slower (even with @~@ put in
-- 'BuiltinRuntime' in the places where it's necessary to have laziness for evaluators to work).

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

import Control.Monad.Except
import Data.Array
import Data.Kind qualified as GHC
import Data.Proxy
import Data.Some.GADT
import GHC.Exts (inline)
import GHC.TypeLits

-- | Turn a list of Haskell types @args@ into a functional type ending in @res@.
--
-- >>> :set -XDataKinds
-- >>> :kind! FoldArgs [Text, Bool] Integer
-- FoldArgs [Text, Bool] Integer :: *
-- = Text -> Bool -> Integer
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
data BuiltinMeaning val cost =
    forall args res. BuiltinMeaning
        (TypeScheme val args res)
        (FoldArgs args res)
        (BuiltinRuntimeOptions (Length args) val cost)

-- | A type class for \"each function from a set of built-in functions has a 'BuiltinMeaning'\".
class (Bounded fun, Enum fun, Ix fun) => ToBuiltinMeaning uni fun where
    -- | The @cost@ part of 'BuiltinMeaning'.
    type CostingPart uni fun

    -- | Get the 'BuiltinMeaning' of a built-in function.
    toBuiltinMeaning :: HasConstantIn uni val => fun -> BuiltinMeaning val (CostingPart uni fun)

-- | Get the type of a built-in function.
typeOfBuiltinFunction :: ToBuiltinMeaning uni fun => fun -> Type TyName uni ()
typeOfBuiltinFunction fun = case toBuiltinMeaning @_ @_ @(Term TyName Name _ _ ()) fun of
    BuiltinMeaning sch _ _ -> typeSchemeToType sch

{- Note [Automatic derivation of type schemes]
We use two type classes for automatic derivation of type schemes: 'KnownMonotype' and
'KnownPolytype'. The terminology is due to https://en.wikipedia.org/wiki/Hindley%E2%80%93Milner_type_system#The_Hindley%E2%80%93Milner_type_system

'KnownMonotype' and 'KnownPolytype' are responsible for deriving monomorphic and polymorphic types,
respectively. 'KnownMonotype' turns every argument that the Haskell denotation of a builtin
receives into a 'TypeSchemeArrow'. We extract the arguments from the type of the Haskell denotation
using the 'GetArgs' type family. 'KnownPolytype' turns every bound variable into a 'TypeSchemeAll'.
We extract variables from the type of the Haskell denotation using the 'ToBinds' type family
(in particular, see the @ToBinds (TypeScheme val args res)@ type instances). Variables are
collected in the order that they appear in (i.e. just like in Haskell). For example, processing
a type signature like

    const
        :: ( a ~ Opaque val (TyVarRep ('TyNameRep "a" 0))
           , b ~ Opaque val (TyVarRep ('TyNameRep "b" 1))
           )
        => b -> a -> b

with 'ToBinds' results in the following list of bindings:

    '[ 'Some ('TyNameRep "b" 1), 'Some ('TyNameRep "a" 0) ]

Higher-kinded type variables are fully supported.

The implementations of the 'KnownMonotype' and 'KnownPolytype' classes are structured in an
inference-friendly manner:

1. we compute @args@ using a type family ('GetArgs') in order to dispatch on the list of
   arguments of a built-in function in a way that doesn't force us to introduce overlapping
   instances
2. the @a -> res@ dependency allows us not to compute @res@ using a type family like with @args@
3. the @args res -> a@ dependency allows us not to mention @a@ in the type of 'knownMonotype'

Polymorphic built-in functions are handled via automatic specialization of all Haskell type
variables as types representing PLC type variables, as long as each Haskell variable appears as a
left argument to @(->)@ and is not buried somewhere inside (i.e. automatic derivation can handle
neither @f a@, @ListRep a@, nor @f Int@. Nor is @a -> b@ allowed to the left of an @(->)@.
Where all lower-case names are Haskell type variables). We'll call functions having such types
"simply-polymorphic". See the docs of 'EnumerateFromTo' for details.

The end result is that the user only has to specify the type of the denotation of a built-in
function and the 'TypeScheme' of the built-in function will be derived automatically. And in the
monomorphic and simply-polymorphic cases no types need to be specified at all.
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
-- unfolding not working for recursive functions and 'TypeScheme' is recursive, i.e. the conversion
-- can only be a recursive function), and so it would cause us to retain a lot of
-- evaluation-irrelevant stuff in the constructors of 'TypeScheme', which makes it much harder to
-- read the Core. Technically speaking, we could convert a 'TypeScheme' to a 'RuntimeScheme'
-- statically if we changed the definition of 'TypeScheme' and made it a singleton, but then the
-- conversion function would have to become a class anyway and we'd just replicate what we have here,
-- except in a much more complicated way.
-- It's also more efficient to generate 'RuntimeScheme's directly, but that shouldn't really matter, -- given that they computed only once and cached afterwards.
--
-- Similarly, we could've computed 'toImmediateF' and 'toDeferredF' from a 'TypeScheme' but not
-- statically again, and that would break inlining and basically all the optimization.
class KnownMonotype val args res a | args res -> a, a -> res where
    knownMonotype :: TypeScheme val args res
    knownMonoruntime :: RuntimeScheme (Length args)

    -- | Convert the denotation of a builtin to its runtime counterpart with immediate unlifting.
    toImmediateF :: FoldArgs args res -> ToRuntimeDenotationType val (Length args)

    -- | Convert the denotation of a builtin to its runtime counterpart with deferred unlifting.
    -- The argument is in 'ReadKnownM', because that's what deferred unlifting amounts to:
    -- passing the action returning the builtin application around until full saturation, which is
    -- when the action actually gets run.
    toDeferredF :: ReadKnownM () (FoldArgs args res) -> ToRuntimeDenotationType val (Length args)

-- | Once we've run out of term-level arguments, we return a 'TypeSchemeResult'.
instance (res ~ res', KnownTypeAst (UniOf val) res, MakeKnown val res) =>
            KnownMonotype val '[] res res' where
    knownMonotype = TypeSchemeResult
    knownMonoruntime = RuntimeSchemeResult

    toImmediateF = makeKnown (Just ())
    {-# INLINE toImmediateF #-}

    -- For deferred unlifting we need to lift the 'ReadKnownM' action into 'MakeKnownM',
    -- hence 'liftEither'.
    toDeferredF getRes = liftEither getRes >>= makeKnown (Just ())
    {-# INLINE toDeferredF #-}

-- | Every term-level argument becomes as 'TypeSchemeArrow'.
instance
        ( KnownTypeAst (UniOf val) arg, MakeKnown val arg, ReadKnown val arg
        , KnownMonotype val args res a
        ) => KnownMonotype val (arg ': args) res (arg -> a) where
    knownMonotype = TypeSchemeArrow knownMonotype
    knownMonoruntime = RuntimeSchemeArrow $ knownMonoruntime @val @args @res

    -- Unlift, then recurse.
    toImmediateF f = fmap (toImmediateF @val @args @res . f) . readKnown (Just ())
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
        -- builtin is not supposed to throw an exception at any stage, that would be a bug regardless
        -- of how unlifting is aligned.
        --
        -- 'pure' signifies that no failure can occur at this point.
        pure . toDeferredF @val @args @res $! getF <*> readKnown (Just ()) arg
    {-# INLINE toDeferredF #-}

-- | A class that allows us to derive a polytype for a builtin.
class KnownMonotype val args res a =>
        KnownPolytype (binds :: [Some TyNameRep]) val args res a | args res -> a, a -> res where
    knownPolytype :: TypeScheme val args res
    knownPolyruntime :: RuntimeScheme (Length args)

-- | Once we've run out of type-level arguments, we start handling term-level ones.
instance KnownMonotype val args res a => KnownPolytype '[] val args res a where
    knownPolytype = knownMonotype
    knownPolyruntime = knownMonoruntime @val @args @res

-- Here we unpack an existentially packed @kind@ and constrain it afterwards!
-- So promoted existentials are true sigmas! If we were at the term level, we'd have to pack
-- @kind@ along with the @KnownKind kind@ constraint, otherwise when we unpack the existential,
-- all information is lost and we can't do anything with @kind@.
-- | Every type-level argument becomes a 'TypeSchemeAll'.
instance (KnownSymbol name, KnownNat uniq, KnownKind kind, KnownPolytype binds val args res a) =>
            KnownPolytype ('Some ('TyNameRep @kind name uniq) ': binds) val args res a where
    knownPolytype = TypeSchemeAll @name @uniq @kind Proxy $ knownPolytype @binds
    knownPolyruntime = RuntimeSchemeAll $ knownPolyruntime @binds @val @args @res

-- See Note [Automatic derivation of type schemes]
-- | Construct the meaning for a built-in function by automatically deriving its
-- 'TypeScheme', given
--
-- 1. the denotation of the builtin
-- 2. an uninstantiated costing function
makeBuiltinMeaning
    :: forall a val cost binds args res j.
       ( binds ~ ToBinds a, args ~ GetArgs a, a ~ FoldArgs args res
       , ElaborateFromTo 0 j val a, KnownPolytype binds val args res a
       )
    => a -> (cost -> ToCostingType (Length args)) -> BuiltinMeaning val cost
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
-- | Calculate runtime info for all built-in functions given denotations of builtins
-- and a cost model.
toBuiltinsRuntime
    :: (cost ~ CostingPart uni fun, HasConstantIn uni val, ToBuiltinMeaning uni fun)
    => UnliftingMode -> cost -> BuiltinsRuntime fun val
toBuiltinsRuntime unlMode cost =
    let arr = tabulateArray $ toBuiltinRuntime unlMode cost . inline toBuiltinMeaning
     in -- Force array elements to WHNF
        foldr seq (BuiltinsRuntime arr) arr
{-# INLINE toBuiltinsRuntime #-}
