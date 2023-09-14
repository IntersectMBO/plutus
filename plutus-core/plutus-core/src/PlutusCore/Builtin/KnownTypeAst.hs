-- editorconfig-checker-disable-file
{-# LANGUAGE AllowAmbiguousTypes      #-}
{-# LANGUAGE ConstraintKinds          #-}
{-# LANGUAGE DataKinds                #-}
{-# LANGUAGE DefaultSignatures        #-}
{-# LANGUAGE FlexibleInstances        #-}
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
    , HasTermLevel
    , HasTypeLevel
    , HasTypeAndTermLevel
    , mkTyBuiltin
    , TypeHole
    , KnownBuiltinTypeAst
    , KnownTypeAst (..)
    , Insert
    , Delete
    ) where

import PlutusCore.Builtin.Emitter
import PlutusCore.Builtin.KnownKind
import PlutusCore.Builtin.Polymorphism
import PlutusCore.Core
import PlutusCore.Evaluation.Result
import PlutusCore.Name
import PlutusCore.Subst (typeMapNames)

import Data.Kind qualified as GHC (Constraint, Type)
import Data.Proxy
import Data.Some.GADT qualified as GADT
import Data.Text qualified as Text
import Data.Type.Bool
import Data.Void
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

{- Note [Name generality of KnownTypeAst]
The 'KnownTypeAst' class takes a @tyname@ argument. The reason for this is that we want to be able
to define 'mkTyBuiltin' such that it's generic over the type of names, because in addition to
'TyName' we also have 'TyDeBruijn' and it's convenient to seemlessly embed built-in types into a
'Type' regardless of which kind of names it expects.

However we don't want that @tyname@ to proliferate through the entire code base. For example,
'HasTypeLevel' propagates up to PlutusTx and it doesn't make sense to mention implementation details
such as 'TyName' there. For this reason we instantiate @tyname@ as soon as possible. When we want
and can have full generality, we instantiate @tyname@ with 'Void', because anything can be recovered
from 'Void' via 'absurd' while allowing us not to thread the @tyname@ parameter through half the
codebase. And when we don't want or can't have generality, we instantiate @tyname@ with 'TyName'.
-}

-- | Specifies that the given type is a built-in one and can be embedded into a 'Type'.
type HasTypeLevel :: forall a. (GHC.Type -> GHC.Type) -> a -> GHC.Constraint
type HasTypeLevel uni x = KnownTypeAst Void uni (ElaborateBuiltin uni x)

-- | The product of 'HasTypeLevel' and 'HasTermLevel'.
type HasTypeAndTermLevel :: forall a. (GHC.Type -> GHC.Type) -> a -> GHC.Constraint
type HasTypeAndTermLevel uni x = (uni `HasTypeLevel` x, uni `HasTermLevel` x)

-- See Note [Name generality of KnownTypeAst].
-- TODO: make it @forall {a}@ once we have that.
-- (see https://github.com/ghc-proposals/ghc-proposals/blob/master/proposals/0099-explicit-specificity.rst)
-- | Convert a Haskell representation of a possibly 0-ary application of a built-in type to
-- arbitrary types implementing 'KnownTypeAst'.
mkTyBuiltin :: forall a (x :: a) uni ann tyname. uni `HasTypeLevel` x => ann -> Type tyname uni ann
mkTyBuiltin ann = ann <$ typeMapNames absurd (toTypeAst $ Proxy @(ElaborateBuiltin uni x))
{-# INLINE mkTyBuiltin #-}

-- | A constraint for \"@a@ is a 'KnownTypeAst' by means of being included in @uni@\".
type KnownBuiltinTypeAst :: forall a. GHC.Type -> (GHC.Type -> GHC.Type) -> a -> GHC.Constraint
type KnownBuiltinTypeAst tyname uni x = AllBuiltinArgs uni (KnownTypeAst tyname uni) x

-- See Note [Name generality of KnownTypeAst].
-- | This class allows one to convert the type-level Haskell representation of a Plutus type into
-- the corresponding Plutus type. Associated type families are needed to help elaboration.
--
-- Depending on the universe converting a Haskell type to a Plutus team can give different results
-- (e.g. 'Int' can be a built-in type instead of being encoded via built-in 'Integer'), hence this
-- class takes a @uni@ argument. Plus, elaboration is universe-specific too.
type KnownTypeAst :: forall a. GHC.Type -> (GHC.Type -> GHC.Type) -> a -> GHC.Constraint
class KnownTypeAst tyname uni x where
    -- | Whether @x@ is a built-in type.
    type IsBuiltin uni x :: Bool
    type IsBuiltin uni x = IsBuiltin uni (ElaborateBuiltin uni x)

    -- | Return every part of the type that can be a to-be-instantiated type variable.
    -- For example, in @Integer@ there's no such types and in @(a, b)@ it's the two arguments
    -- (@a@ and @b@) and the same applies to @a -> b@ (to mention a type that is not built-in).
    type ToHoles uni x :: [Hole]
    type ToHoles uni x = ToHoles uni (ElaborateBuiltin uni x)

    -- | Collect all unique variables (a variable consists of a textual name, a unique and a kind)
    -- in an accumulator and return the accumulator once a leaf is reached.
    type ToBinds uni (acc :: [GADT.Some TyNameRep]) x :: [GADT.Some TyNameRep]
    type ToBinds uni acc x = ToBinds uni acc (ElaborateBuiltin uni x)

    -- | Return the Plutus counterpart of the @x@ type.
    toTypeAst :: proxy x -> Type tyname uni ()
    default toTypeAst
        :: KnownTypeAst tyname uni (ElaborateBuiltin uni x) => proxy x -> Type tyname uni ()
    toTypeAst _ = toTypeAst (Proxy @(ElaborateBuiltin uni x))
    {-# INLINE toTypeAst #-}

instance KnownTypeAst tyname uni a => KnownTypeAst tyname uni (EvaluationResult a) where
    type IsBuiltin _ (EvaluationResult a) = 'False
    type ToHoles _ (EvaluationResult a) = '[TypeHole a]
    type ToBinds uni acc (EvaluationResult a) = ToBinds uni acc a
    toTypeAst _ = toTypeAst $ Proxy @a
    {-# INLINE toTypeAst #-}

instance KnownTypeAst tyname uni a => KnownTypeAst tyname uni (Emitter a) where
    type IsBuiltin _ (Emitter a) = 'False
    type ToHoles _ (Emitter a) = '[TypeHole a]
    type ToBinds uni acc (Emitter a) = ToBinds uni acc a
    toTypeAst _ = toTypeAst $ Proxy @a
    {-# INLINE toTypeAst #-}

instance KnownTypeAst tyname uni rep => KnownTypeAst tyname uni (SomeConstant uni rep) where
    type IsBuiltin _ (SomeConstant uni rep) = 'False
    type ToHoles _ (SomeConstant _ rep) = '[RepHole rep]
    type ToBinds uni acc (SomeConstant _ rep) = ToBinds uni acc rep
    toTypeAst _ = toTypeAst $ Proxy @rep
    {-# INLINE toTypeAst #-}

instance KnownTypeAst tyname uni rep => KnownTypeAst tyname uni (Opaque val rep) where
    type IsBuiltin _ (Opaque val rep) = 'False
    type ToHoles _ (Opaque _ rep) = '[RepHole rep]
    type ToBinds uni acc (Opaque _ rep) = ToBinds uni acc rep
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

instance uni `Contains` f => KnownTypeAst tyname uni (BuiltinHead f) where
    type IsBuiltin _ (BuiltinHead f) = 'True
    type ToHoles _ (BuiltinHead f) = '[]
    type ToBinds _ acc (BuiltinHead f) = acc
    toTypeAst _ = TyBuiltin () $ someType @_ @f
    {-# INLINE toTypeAst #-}

instance (KnownTypeAst tyname uni a, KnownTypeAst tyname uni b) =>
        KnownTypeAst tyname uni (a -> b) where
    type IsBuiltin _ (a -> b) = 'False
    type ToHoles _ (a -> b) = '[TypeHole a, TypeHole b]
    type ToBinds uni acc (a -> b) = ToBinds uni (ToBinds uni acc a) b
    toTypeAst _ = TyFun () (toTypeAst $ Proxy @a) (toTypeAst $ Proxy @b)
    {-# INLINE toTypeAst #-}

instance (tyname ~ TyName, name ~ 'TyNameRep text uniq, KnownSymbol text, KnownNat uniq) =>
            KnownTypeAst tyname uni (TyVarRep name) where
    type IsBuiltin _ (TyVarRep name) = 'False
    type ToHoles _ (TyVarRep name) = '[]
    type ToBinds _ acc (TyVarRep name) = Insert ('GADT.Some name) acc
    toTypeAst _ = TyVar () . toTyNameAst $ Proxy @('TyNameRep text uniq)
    {-# INLINE toTypeAst #-}

instance (KnownTypeAst tyname uni fun, KnownTypeAst tyname uni arg) =>
        KnownTypeAst tyname uni (TyAppRep fun arg) where
    type IsBuiltin uni (TyAppRep fun arg) = IsBuiltin uni fun && IsBuiltin uni arg
    type ToHoles _ (TyAppRep fun arg) = '[RepHole fun, RepHole arg]
    type ToBinds uni acc (TyAppRep fun arg) = ToBinds uni (ToBinds uni acc fun) arg
    toTypeAst _ = TyApp () (toTypeAst $ Proxy @fun) (toTypeAst $ Proxy @arg)
    {-# INLINE toTypeAst #-}

instance
        ( tyname ~ TyName, name ~ 'TyNameRep @kind text uniq, KnownSymbol text, KnownNat uniq
        , KnownKind kind, KnownTypeAst tyname uni a
        ) => KnownTypeAst tyname uni (TyForallRep name a) where
    type IsBuiltin _ (TyForallRep name a) = 'False
    type ToHoles _ (TyForallRep name a) = '[RepHole a]
    type ToBinds uni acc (TyForallRep name a) = Delete ('GADT.Some name) (ToBinds uni acc a)
    toTypeAst _ =
        TyForall ()
            (toTyNameAst $ Proxy @('TyNameRep text uniq))
            (demoteKind $ knownKind @kind)
            (toTypeAst $ Proxy @a)
    {-# INLINE toTypeAst #-}

-- Utils

-- | Insert @x@ into @xs@ unless it's already there.
type Insert :: forall a. a -> [a] -> [a]
type family Insert x xs where
    Insert x '[]      = '[x]
    Insert x (x : xs) = x ': xs
    Insert x (y : xs) = y ': Insert x xs

-- | Delete the first @x@ from a list. Which is okay since we only ever put things in once.
type Delete :: forall a. a -> [a] -> [a]
type family Delete x xs where
    Delete _ '[]       = '[]
    Delete x (x ': xs) = xs
    Delete x (y ': xs) = y ': Delete x xs
