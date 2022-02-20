-- GHC doesn't like the definition of 'makeBuiltinMeaning'.
{-# OPTIONS_GHC -fno-warn-redundant-constraints #-}

{-# LANGUAGE AllowAmbiguousTypes       #-}
{-# LANGUAGE DataKinds                 #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE FunctionalDependencies    #-}
{-# LANGUAGE PolyKinds                 #-}
{-# LANGUAGE TypeApplications          #-}
{-# LANGUAGE TypeFamilies              #-}
{-# LANGUAGE TypeOperators             #-}
{-# LANGUAGE UndecidableInstances      #-}

-- DO NOT enable @StrictData@ in this file as it makes the evaluator slower (even with @~@ put in
-- 'BuiltinRuntime' in the places where it's necessary to have laziness for evaluators to work).

module PlutusCore.Builtin.Meaning where

import PlutusCore.Builtin.Elaborate
import PlutusCore.Builtin.HasConstant
import PlutusCore.Builtin.KnownKind
import PlutusCore.Builtin.KnownType
import PlutusCore.Builtin.KnownTypeAst
import PlutusCore.Builtin.TypeScheme
import PlutusCore.Core
import PlutusCore.Name

import Data.Array
import Data.Kind qualified as GHC
import Data.Proxy
import Data.Some.GADT
import GHC.Exts (inline)
import GHC.TypeLits

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
        (cost -> FoldArgsEx args)
-- I tried making it @(forall val. HasConstantIn uni val => TypeScheme val args res)@ instead of
-- @TypeScheme val args res@, but 'makeBuiltinMeaning' has to talk about
-- @KnownPolytype binds val args res a@ (note the @val@), because instances of 'KnownMonotype'
-- are constrained with @KnownType val arg@ and @KnownType val res@, and so the earliest we can
-- generalize from @val@ to @UniOf val@ is in 'toBuiltinMeaning'.
-- Besides, for 'BuiltinRuntime' we want to have a concrete 'TypeScheme' anyway for performance
-- reasons (there isn't much point in caching a value of a type with a constraint as it becomes a
-- function at runtime anyway, due to constraints being compiled as dictionaries).

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

The 'INLINE' pragmas are required for this stuff to be
-}

type family GetArgs a :: [GHC.Type] where
    GetArgs (a -> b) = a ': GetArgs b
    GetArgs _        = '[]

-- | A class that allows us to derive a monotype for a builtin.
class KnownMonotype val args res a | args res -> a, a -> res where
    knownMonotype :: TypeScheme val args res

-- | Once we've run out of term-level arguments, we return a 'TypeSchemeResult'.
instance (res ~ res', KnownType val res) => KnownMonotype val '[] res res' where
    knownMonotype = TypeSchemeResult

-- | Every term-level argument becomes as 'TypeSchemeArrow'.
instance (KnownType val arg, KnownMonotype val args res a) =>
            KnownMonotype val (arg ': args) res (arg -> a) where
    -- The call to 'inline' was added because without it 'readKnown' was not getting inlined for
    -- certain types (in particular, 'Int' and 'Opaque').
    knownMonotype = TypeSchemeArrow (inline readKnown) knownMonotype

-- | A class that allows us to derive a polytype for a builtin.
class KnownPolytype (binds :: [Some TyNameRep]) val args res a | args res -> a, a -> res where
    knownPolytype :: TypeScheme val args res

-- | Once we've run out of type-level arguments, we start handling term-level ones.
instance KnownMonotype val args res a => KnownPolytype '[] val args res a where
    knownPolytype = knownMonotype

-- Here we unpack an existentially packed @kind@ and constrain it afterwards!
-- So promoted existentials are true sigmas! If we were at the term level, we'd have to pack
-- @kind@ along with the @KnownKind kind@ constraint, otherwise when we unpack the existential,
-- all information is lost and we can't do anything with @kind@.
-- | Every type-level argument becomes a 'TypeSchemeAll'.
instance (KnownSymbol name, KnownNat uniq, KnownKind kind, KnownPolytype binds val args res a) =>
            KnownPolytype ('Some ('TyNameRep @kind name uniq) ': binds) val args res a where
    knownPolytype = TypeSchemeAll @name @uniq @kind Proxy $ knownPolytype @binds

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
    => a -> (cost -> FoldArgsEx args) -> BuiltinMeaning val cost
makeBuiltinMeaning = BuiltinMeaning $ knownPolytype @binds @val @args @res
