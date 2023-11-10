-- editorconfig-checker-disable-file
-- GHC doesn't like the definition of 'TrySpecializeAsVar'.
{-# OPTIONS_GHC -fno-warn-redundant-constraints #-}

{-# LANGUAGE ConstraintKinds          #-}
{-# LANGUAGE DataKinds                #-}
{-# LANGUAGE FlexibleInstances        #-}
{-# LANGUAGE FunctionalDependencies   #-}
{-# LANGUAGE PolyKinds                #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeApplications         #-}
{-# LANGUAGE TypeFamilies             #-}
{-# LANGUAGE TypeOperators            #-}
{-# LANGUAGE UndecidableInstances     #-}

module PlutusCore.Builtin.Elaborate
  ( ElaborateFromTo
  ) where

import PlutusCore.Builtin.KnownTypeAst
import PlutusCore.Builtin.Polymorphism
import PlutusCore.Core.Type

import Data.Kind qualified as GHC
import Data.Type.Bool
import Data.Type.Equality
import GHC.TypeLits

-- | Check if two values of different kinds are in fact the same value (with the same kind).
-- A heterogeneous version of @Type.Equality.(==)@.
type (===) :: forall a b. a -> b -> Bool
type family x === y where
    x === x = 'True
    x === y = 'False

-- Explained in detail in https://github.com/effectfully-ou/sketches/tree/cbf3ee9d11e0e3d4fc397ce7bf419418224122e2/poly-type-of-saga/part1-try-unify
-- | Unify two values if possible, otherwise leave them alone. Useful for instantiating type
-- variables.
type TryUnify :: forall a b. Bool -> a -> b -> GHC.Constraint
class same ~ (x === y) => TryUnify same x y
instance (x === y) ~ 'False => TryUnify 'False x y
instance {-# INCOHERENT #-} (x ~~ y, same ~ 'True) => TryUnify same x y

-- | Unify two values unless they're obviously distinct (in which case do nothing).
-- Allows us to detect and specialize type variables, since a type variable is not obviously
-- distinct from anything else and so the INCOHERENT instance of 'TryUnify' gets triggered and the
-- variable gets unified with whatever we want it to.
type (~?~) :: forall a b. a -> b -> GHC.Constraint
type x ~?~ y = TryUnify (x === y) x y

-- | Get the element at an @i@th position in a list.
type Lookup :: forall a. Nat -> [a] -> a
type family Lookup n xs where
    Lookup _ '[]       = TypeError ('Text "Not enough elements")
    Lookup 0 (x ': xs) = x
    Lookup n (_ ': xs) = Lookup (n - 1) xs

-- | Get the name at the @i@th position in the list of default names. We could use @a_0@, @a_1@,
-- @a_2@ etc instead, but @a@, @b@, @c@ etc are nicer.
type GetName :: GHC.Type -> Nat -> Symbol
type family GetName k i where
    GetName GHC.Type i = Lookup i '["a", "b", "c", "d", "e", "i", "j", "k", "l"]
    GetName _        i = Lookup i '["f", "g", "h", "m", "n"]  -- For higher-kinded types.

-- | Apply the function stored in the provided 'Maybe' if there's one.
type MaybeApply :: forall k. Maybe (k -> k) -> k -> k
type family MaybeApply mayVal x where
    MaybeApply 'Nothing  a = a
    MaybeApply ('Just f) a = f a

-- | Try to specialize @a@ as a type representing a PLC type variable.
-- @i@ is a fresh id and @j@ is a final one (either @i + 1@ or @i@ depending on whether
-- specialization attempt is successful or not).
-- @mw@ is for wrapping 'TyVarRep', if there's a wrapper inside (see 'HandleHole' for how it's
-- used).
type TrySpecializeAsVar :: forall k. Nat -> Nat -> Maybe (k -> k) -> k -> GHC.Constraint
class TrySpecializeAsVar i j mw a | i mw a -> j
instance
    ( var ~ MaybeApply mw (TyVarRep @k ('TyNameRep (GetName k i) i))
    -- Try to unify @a@ with a freshly created @var@.
    , a ~?~ var
    -- If @a@ is equal to @var@ then unification was successful and we just used the fresh id and
    -- so we need to bump it up. Otherwise @var@ was discarded and so the fresh id is still fresh.
    -- Replacing @(===)@ with @(==)@ causes errors at use site, for whatever reason.
    , j ~ If (a === var) (i + 1) i
    ) => TrySpecializeAsVar i j mw (a :: k)

type NoAppliedVarsHeader =
    'Text "A built-in function is not allowed to have applied type variables in its type"

-- See Note [Rep vs Type context].
-- | Throw an error telling the user not to apply type variables to anything.
type ThrowNoAppliedVars :: (GHC.Type -> GHC.Type) -> GHC.Constraint
type family ThrowNoAppliedVars hole where
    -- In the Rep context higher-kinded type variables are allowed, but need to be applied via
    -- 'TyAppRep', hence the error message.
    ThrowNoAppliedVars RepHole = TypeError
        ( NoAppliedVarsHeader
        ':$$: 'Text "To fix this error apply type variables via explicit ‘TyAppRep’"
        )
    -- In the Type context no higher-kinded type variables are allowed.
    ThrowNoAppliedVars TypeHole = TypeError
        ( NoAppliedVarsHeader
        ':$$: 'Text "To fix this error specialize all higher-kinded type variables"
        )
    -- In case we add more contexts.
    ThrowNoAppliedVars _ = TypeError
        ( NoAppliedVarsHeader
        ':$$: 'Text "Internal error: the context is not recognized. Please report"
        )

-- See Note [Elaboration of higher-kinded type variables].
-- | Check that the higher-kinded type does not represent a PLC type variable and if it does.
type CheckNotAppliedVar :: forall k. (GHC.Type -> GHC.Type) -> k -> GHC.Constraint
type family CheckNotAppliedVar hole a where
    CheckNotAppliedVar hole (TyVarRep _) = ThrowNoAppliedVars hole
    CheckNotAppliedVar _    _            = ()

-- | Try to specialize the head of a (possibly nullary) type application to a type representing a
-- PLC variable and throw if that succeeds or if it already was one.
type TrySpecializeHeadAsVar
    :: forall a b. Nat -> Nat -> (GHC.Type -> GHC.Type) -> (a -> b) -> GHC.Constraint
class TrySpecializeHeadAsVar i j hole f | i f -> j
-- | Recurse to reach the head.
instance {-# OVERLAPPABLE #-}
    TrySpecializeHeadAsVar i j hole f => TrySpecializeHeadAsVar i j hole (f x)
-- | Reached the head, it's a 'TyVarRep', throwing. Mostly to ensure that a 'TyVarRep' doesn't slip
-- in via user input, but also out of pure paranoia (GHC seems to occasionally solve constraints
-- for the same type multiple times by racing through different routes in the presence of
-- @INCOHERENT@ pragmas, but this is not confirmed. It wouldn't be unreasonable, though).
instance {-# OVERLAPPING #-}
    (ThrowNoAppliedVars hole, i ~ j) => TrySpecializeHeadAsVar i j hole (TyVarRep name)
-- | Reached the head, try to specialize it as a variable and throw if that succeeds.
instance {-# INCOHERENT #-}
    ( TrySpecializeAsVar i j 'Nothing f
    , CheckNotAppliedVar hole f
    ) => TrySpecializeHeadAsVar i j hole f

{- | Try to specialize @a@ as a type representing a PLC type variable.
Same as 'TrySpecializeAsVar' (in particular, the parameters are the same), except this one also
checks if the given type is a type application, in which case it tries to specialize the head of the
application to a type representing a PLC type variable and throws if that succeeds.

We need this because blindly specializing an @f A@ (where @f@ is a type variable and @A@ is an
arbitrary type) in the Type context would give us @Opaque val A@ (by @f ~ Opaque val@) instead of
@Opaque val (f' A)@, which would be very confusing to the user: the only reasonable way to elaborate
an application of a type variable in Haskell is to make an application of a type variable in PLC,
not to randomly drop the type variable.

There's no way we could elaborate an applied type variable without surprising the user, because no
instantiation of @f@ could turn @f A@ into @Opaque val (f' A)@, hence we simply forbid applied type
variables and throw upon encountering one. It would be a pain to handle an iterated application of a
type representing a PLC type variable anyway.

It's not possible to determine if @Opaque val A@ is a specialization of @f a@ or @a@ (for a type
variable @a@), hence we have to make this whole check during elaboration and not any later.

Regardless of whether the given argument is a type application or not, it's attempted to be
specialized as a type representing a PLC type variable, because such a type is a type application
itself. Unifying an already known type variable with a fresh one is useful when the name part
of the former is unknown.
-}
type TrySpecializeAsUnappliedVar
    :: forall k. Nat -> Nat -> (GHC.Type -> GHC.Type) -> Maybe (k -> k) -> k -> GHC.Constraint
class TrySpecializeAsUnappliedVar i j hole mw a | i mw a -> j
instance
    ( TrySpecializeHeadAsVar i j hole f
    , TrySpecializeAsVar j k mw (f x)
    ) => TrySpecializeAsUnappliedVar i k hole mw (f x)
instance {-# INCOHERENT #-} TrySpecializeAsVar i j mw a => TrySpecializeAsUnappliedVar i j hole mw a

-- See Note [Rep vs Type context]
-- | First try to specialize the hole using 'TrySpecializeAsVar' and then recurse on the result of
-- that using 'HandleHoles'.
-- @i@ is a fresh id and @j@ is a final one as in 'TrySpecializeAsVar', but since 'HandleHole' can
-- specialize multiple variables, @j@ can be equal to @i + n@ for any @n@ (including @0@).
type HandleHole :: (GHC.Type -> GHC.Type) -> Nat -> Nat -> GHC.Type -> Hole -> GHC.Constraint
class HandleHole uni i j val hole | uni i val hole -> j
-- In the Rep context @x@ is attempted to be specialized as a 'TyVarRep'.
instance
    ( TrySpecializeAsUnappliedVar i j RepHole 'Nothing x
    , HandleHoles uni j k val x
    ) => HandleHole uni i k val (RepHole x)
-- In the Type context @a@ is attempted to be specialized as a 'TyVarRep' wrapped in @Opaque val@.
instance
    ( TrySpecializeAsUnappliedVar i j TypeHole ('Just (Opaque val)) a
    , HandleHoles uni j k val a
    ) => HandleHole uni i k val (TypeHole a)

-- | Call 'HandleHole' over each hole from the list, threading the state (the fresh unique) through
-- the calls.
type HandleHolesGo :: (GHC.Type -> GHC.Type) -> Nat -> Nat -> GHC.Type -> [Hole] -> GHC.Constraint
class HandleHolesGo uni i j val holes | uni i val holes -> j
instance i ~ j => HandleHolesGo uni i j val '[]
instance
    ( HandleHole uni i j val hole
    , HandleHolesGo uni j k val holes
    ) => HandleHolesGo uni i k val (hole ': holes)

-- | If the outermost constructor of the second argument is known and happens to be one of the
-- constructors of the list data type, then the second argument is returned back. Otherwise the
-- first one is returned, which is meant to be a custom type error.
type ThrowOnStuckList :: forall a. [a] -> [a] -> [a]
type family ThrowOnStuckList err xs where
    ThrowOnStuckList _   '[]       = '[]
    ThrowOnStuckList _   (x ': xs) = x ': xs
    ThrowOnStuckList err _         = err

type UnknownTypeError :: forall a any. GHC.Type -> a -> any
type family UnknownTypeError val x where
    UnknownTypeError val x = TypeError
        (         'Text "No instance for ‘KnownTypeAst "
            ':<>: 'ShowType (UniOf val)
            ':<>: 'Text " ("
            ':<>: 'ShowType x
            ':<>: 'Text ")’"
        ':$$: 'Text "Which means"
        ':$$: 'Text "  ‘" ':<>: 'ShowType x ':<>: 'Text "’"
        ':$$: 'Text "is neither a built-in type, nor one of the control types."
        ':$$: 'Text "If it can be represented in terms of one of the built-in types"
        ':$$: 'Text "  then go add the instance (you may need a few others too)"
        ':$$: 'Text "  alongside the instance for the built-in type."
        ':$$: 'Text "Otherwise you may need to add a new built-in type"
        ':$$: 'Text "  (provided you're doing something that can be supported in principle)"
        )

-- | Get the holes of @x@ and recurse into them.
type HandleHoles
    :: forall a. (GHC.Type -> GHC.Type) -> Nat -> Nat -> GHC.Type -> a -> GHC.Constraint
type HandleHoles uni i j val x =
    -- Here we detect a stuck application of 'ToHoles' and throw 'UnknownTypeError' on it.
    -- See https://blog.csongor.co.uk/report-stuck-families for a detailed description of how
    -- detection of stuck type families works.
    HandleHolesGo uni i j val (ThrowOnStuckList (UnknownTypeError val x) (ToHoles uni x))

-- Check out the following for a detailed explanation of the idea (after learning about 'TryUnify'):
-- https://github.com/effectfully-ou/sketches/tree/cbf3ee9d11e0e3d4fc397ce7bf419418224122e2/poly-type-of-saga/part2-enumerate-type-vars
-- | Specialize each Haskell type variable in @a@ as a type representing a PLC type variable.
-- @i@ is a fresh id and @j@ is a final one as in 'TrySpecializeAsVar', but since 'HandleHole' can
-- specialize multiple variables, @j@ can be equal to @i + n@ for any @n@ (including @0@).
type ElaborateFromTo
    :: (GHC.Type -> GHC.Type) -> Nat -> Nat -> GHC.Type -> GHC.Type -> GHC.Constraint
type ElaborateFromTo uni i j val a = HandleHole uni i j val (TypeHole a)
