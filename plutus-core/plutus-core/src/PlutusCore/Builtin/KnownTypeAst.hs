{-# LANGUAGE ConstraintKinds          #-}
{-# LANGUAGE DataKinds                #-}
{-# LANGUAGE DefaultSignatures        #-}
{-# LANGUAGE FlexibleInstances        #-}
{-# LANGUAGE KindSignatures           #-}
{-# LANGUAGE MultiParamTypeClasses    #-}
{-# LANGUAGE PolyKinds                #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeApplications         #-}
{-# LANGUAGE TypeFamilies             #-}
{-# LANGUAGE TypeOperators            #-}
{-# LANGUAGE UndecidableInstances     #-}

module PlutusCore.Builtin.KnownTypeAst
    ( TyNameRep (..)
    , TyVarRep
    , TyAppRep
    , TyForallRep
    , Hole
    , RepHole
    , TypeHole
    , KnownBuiltinTypeAst
    , KnownTypeAst (..)
    , Merge
    ) where

import PlutusCore.Builtin.Emitter
import PlutusCore.Builtin.KnownKind
import PlutusCore.Builtin.Polymorphism
import PlutusCore.Core
import PlutusCore.Evaluation.Result
import PlutusCore.MkPlc hiding (error)
import PlutusCore.Name

import Data.Kind qualified as GHC (Constraint, Type)
import Data.Proxy
import Data.Some.GADT qualified as GADT
import Data.Text qualified as Text
import GHC.TypeLits
import Universe

{- Note [Rep vs Type context]
Say you define an @Id@ built-in function and specify its Haskell type signature:

    id :: forall a. a -> a

This gets picked up by the 'TypeScheme' inference machinery, which detects @a@ and instantiates it
to @Opaque val Var0@ where @Var0@ is some concrete type (the exact details don't matter here)
representing a Plutus type variable of kind @*@ with the @0@ unique, so @id@ elaborates to

    id :: Opaque val Var0 -> Opaque val Var0

But consider also the case where you want to define @id@ only over lists. The signature of the
built-in function then is

    idList :: forall a. Opaque val [a] -> Opaque val [a]

Now the 'Opaque' is explicit and the 'TypeScheme' inference machinery needs to go under it in order
to instantiate @a@. Which now does not get instantiated to an 'Opaque' as before, since we're
already inside an 'Opaque' and can just use @Var0@ directly. So @idList@ elaborates to

    idList :: Opaque val [Var0] -> Opaque val [Var0]

Now let's make up some syntax for annotating contexts so that it's clear what's going on:

    idList @Type |
        :: (@Type | Opaque val (@Rep | [Var0]))
        -> (@Type | Opaque val (@Rep | [Var0]))

'@ann |' annotates everything to the right of it. The whole thing then reads as

1. a builtin is always defined in the Type context
2. @->@ preserves the Type context, i.e. it accepts it and passes it down to the domain and codomain
3. @Opaque val@ switches the context from Type to Rep, i.e. it accepts the Type context, but
creates the Rep context for its argument that represents a Plutus type

So why the distinction?

The difference between the Rep and the Type contexts that we've seen so far is that in the Rep
context we don't need any @Opaque@, but this is a very superficial reason to keep the distinction
between contexts, since everything that is legal in the Type context is legal in the Rep context
as well. For example we could've elaborated @idList@ into a bit more verbose

    idList :: Opaque val [Opaque val Var0] -> Opaque val [Opaque val Var0]

and the world wouldn't end because of that, everything would work correctly.

The opposite however is not true: certain types that are legal in the Rep context are not legal in
the Type one and this is the reason why the distinction exists. The simplest example is

    id :: Var0 -> Var0

@Var0@ represents a Plutus type variable and it's a data family with no inhabitants, so it does not
make sense to try to unlift a value of that type.

Now let's say we added a @term@ argument to @Var0@ and said that when @Var0 term@ is a @GHC.Type@,
it has a @term@ inside, just like 'Opaque'. Then we would be able to unlift it, but we also have
things like @TyAppRep@, @TyForallRep@ and that set is open, any Plutus type can be represented
using such combinators and we can even name particular types, e.g. we could have @PlcListRep@,
so we'd have to special-case @GHC.Type@ for each of them and it would be a huge mess.

So instead of mixing up types whose values are actually unliftable with types that are only used
for type checking, we keep the distinction explicit.

The barrier between Haskell and Plutus is the barrier between the Type and the Rep contexts and
that barrier must always be some explicit type constructor that switches the context from Type to
Rep. We've only considered 'Opaque' as an example of such type constructor, but we also have
'SomeConstant' as another example.

Some type constructors turn any context into the Type one, for example 'EvaluationResult' and
'Emitter', although they are useless inside the Rep context, given that it's only for type checking
Plutus and they don't exist in the type language of Plutus.

These @*Rep@ data families like 'TyVarRep', 'TyAppRep' etc all require the Rep context and preserve
it, since they're only for representing Plutus types for type checking purposes.

We call a thing in a Rep or 'Type' context a 'RepHole' or 'TypeHole' respectively. The reason for
the name is that the inference machinery looks at the thing and tries to instantiate it, like fill
a hole.

We could also have a third type of hole/context, Name, because binders bind names rather than
variables and so it makes sense to infer names sometimes, like for 'TyForallRep' for example.
We don't do that currently, because we don't have such builtins anyway.

And there could be even fancier kinds of holes like "infer anything" for cases where the hole
is determined by some other part of the signature. We don't have that either, for the same reason.

For the user defining a builtin this all is pretty much invisible.
-}

-- See Note [Rep vs Type context].
-- | The kind of holes.
data Hole

-- See Note [Rep vs Type context].
-- | A hole in the Rep context.
type RepHole :: forall a hole. a -> hole
data family RepHole x

-- See Note [Rep vs Type context].
-- | A hole in the Type context.
type TypeHole :: forall hole. GHC.Type -> hole
data family TypeHole a

-- | For annotating an uninstantiated built-in type, so that it gets handled by the right instance
-- or type family.
type BuiltinHead :: forall k. k -> k
data family BuiltinHead f

-- | Take an iterated application of a built-in type and elaborate every function application
-- inside of it to 'TypeAppRep', plus annotate the head with 'BuiltinHead'.
-- The idea is that we don't need to process built-in types manually if we simply add some
-- annotations for instance resolution to look for. Think what we'd have to do manually for, say,
-- 'ToHoles': traverse the spine of the application and collect all the holes into a list, which is
-- troubling, because type applications are left-nested and lists are right-nested, so we'd have to
-- use accumulators or an explicit 'Reverse' type family. And then we also have 'KnownTypeAst' and
-- 'ToBinds', so handling built-in types in a special way for each of those would be a hassle,
-- especially given the fact that type-level Haskell is not exactly good at computing things.
-- With the 'ElaborateBuiltin' approach we get 'KnownTypeAst', 'ToHoles' and 'ToBinds' for free.
type ElaborateBuiltin :: forall k. k -> k
type family ElaborateBuiltin a where
    ElaborateBuiltin (f x) = ElaborateBuiltin f `TyAppRep` x
    ElaborateBuiltin f     = BuiltinHead f

-- | A constraint for \"@a@ is a 'KnownTypeAst' by means of being included in @uni@\".
type KnownBuiltinTypeAst uni a = KnownTypeAst uni (ElaborateBuiltin a)

type KnownTypeAst :: forall a. (GHC.Type -> GHC.Type) -> a -> GHC.Constraint
class KnownTypeAst uni x where
    -- | Return every part of the type that can be a to-be-instantiated type variable.
    -- For example, in @Integer@ there's no such types and in @(a, b)@ it's the two arguments
    -- (@a@ and @b@) and the same applies to @a -> b@ (to mention a type that is not built-in).
    type ToHoles x :: [Hole]
    type ToHoles x = ToHoles (ElaborateBuiltin x)

    -- | Collect all unique variables (a variable consists of a textual name, a unique and a kind)
    -- in an @a@.
    type ToBinds x :: [GADT.Some TyNameRep]
    type ToBinds x = ToBinds (ElaborateBuiltin x)

    -- | The type representing @a@ used on the PLC side.
    toTypeAst :: proxy x -> Type TyName uni ()
    default toTypeAst :: KnownBuiltinTypeAst uni x => proxy x -> Type TyName uni ()
    toTypeAst _ = toTypeAst $ Proxy @(ElaborateBuiltin x)
    {-# INLINE toTypeAst #-}

instance KnownTypeAst uni a => KnownTypeAst uni (EvaluationResult a) where
    type ToHoles (EvaluationResult a) = '[TypeHole a]
    type ToBinds (EvaluationResult a) = ToBinds a
    toTypeAst _ = toTypeAst $ Proxy @a
    {-# INLINE toTypeAst #-}

instance KnownTypeAst uni a => KnownTypeAst uni (Emitter a) where
    type ToHoles (Emitter a) = '[TypeHole a]
    type ToBinds (Emitter a) = ToBinds a
    toTypeAst _ = toTypeAst $ Proxy @a
    {-# INLINE toTypeAst #-}

instance KnownTypeAst uni rep => KnownTypeAst uni (SomeConstant uni rep) where
    type ToHoles (SomeConstant _ rep) = '[RepHole rep]
    type ToBinds (SomeConstant _ rep) = ToBinds rep
    toTypeAst _ = toTypeAst $ Proxy @rep
    {-# INLINE toTypeAst #-}

instance KnownTypeAst uni rep => KnownTypeAst uni (Opaque val rep) where
    type ToHoles (Opaque _ rep) = '[RepHole rep]
    type ToBinds (Opaque _ rep) = ToBinds rep
    toTypeAst _ = toTypeAst $ Proxy @rep
    {-# INLINE toTypeAst #-}

toTyNameAst
    :: forall text uniq. (KnownSymbol text, KnownNat uniq)
    => Proxy ('TyNameRep text uniq) -> TyName
toTyNameAst _ =
    TyName $ Name
        (Text.pack $ symbolVal @text Proxy)
        (Unique . fromIntegral $ natVal @uniq Proxy)
{-# INLINE toTyNameAst #-}

instance uni `Contains` f => KnownTypeAst uni (BuiltinHead f) where
    type ToHoles (BuiltinHead f) = '[]
    type ToBinds (BuiltinHead f) = '[]
    toTypeAst _ = mkTyBuiltin @_ @f ()
    {-# INLINE toTypeAst #-}

instance (KnownTypeAst uni a, KnownTypeAst uni b) => KnownTypeAst uni (a -> b) where
    type ToHoles (a -> b) = '[TypeHole a, TypeHole b]
    type ToBinds (a -> b) = Merge (ToBinds a) (ToBinds b)
    toTypeAst _ = TyFun () (toTypeAst $ Proxy @a) (toTypeAst $ Proxy @b)
    {-# INLINE toTypeAst #-}

instance (name ~ 'TyNameRep text uniq, KnownSymbol text, KnownNat uniq) =>
            KnownTypeAst uni (TyVarRep name) where
    type ToHoles (TyVarRep name) = '[]
    type ToBinds (TyVarRep name) = '[ 'GADT.Some name ]
    toTypeAst _ = TyVar () . toTyNameAst $ Proxy @('TyNameRep text uniq)
    {-# INLINE toTypeAst #-}

instance (KnownTypeAst uni fun, KnownTypeAst uni arg) => KnownTypeAst uni (TyAppRep fun arg) where
    type ToHoles (TyAppRep fun arg) = '[RepHole fun, RepHole arg]
    type ToBinds (TyAppRep fun arg) = Merge (ToBinds fun) (ToBinds arg)
    toTypeAst _ = TyApp () (toTypeAst $ Proxy @fun) (toTypeAst $ Proxy @arg)
    {-# INLINE toTypeAst #-}

instance
        ( name ~ 'TyNameRep @kind text uniq, KnownSymbol text, KnownNat uniq
        , KnownKind kind, KnownTypeAst uni a
        ) => KnownTypeAst uni (TyForallRep name a) where
    type ToHoles (TyForallRep name a) = '[RepHole a]
    type ToBinds (TyForallRep name a) = Delete ('GADT.Some name) (ToBinds a)
    toTypeAst _ =
        TyForall ()
            (toTyNameAst $ Proxy @('TyNameRep text uniq))
            (demoteKind $ knownKind @kind)
            (toTypeAst $ Proxy @a)
    {-# INLINE toTypeAst #-}

-- Utils

-- | Delete all @x@s from a list.
type family Delete x xs :: [a] where
    Delete _ '[]       = '[]
    Delete x (x ': xs) = Delete x xs
    Delete x (y ': xs) = y ': Delete x xs

-- | Delete all elements appearing in the first list from the second one and concatenate the lists.
type family Merge xs ys :: [a] where
    Merge '[]       ys = ys
    Merge (x ': xs) ys = x ': Delete x (Merge xs ys)
