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

-- The 'TryUnify' gadget explained in detail in https://github.com/effectfully/sketches/tree/master/poly-type-of-saga/part1-try-unify

-- | Check if two values of different kinds are in fact the same value (with the same kind).
-- A heterogeneous version of @Type.Equality.(==)@.
type (===) :: forall a b. a -> b -> Bool
type family x === y where
    x === x = 'True
    x === y = 'False

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

-- | Like 'id', but a type constructor.
type Id :: forall a. a -> a
data family Id x

-- | Try to specialize @a@ as a type representing a PLC type variable.
-- @i@ is a fresh id and @j@ is a final one (either @i + 1@ or @i@ depending on whether
-- specialization attempt is successful or not).
-- @f@ is for wrapping 'TyVarRep' (see 'HandleHole' for how this is used).
type TrySpecializeAsVar :: forall k. Nat -> Nat -> (k -> k) -> k -> GHC.Constraint
class TrySpecializeAsVar i j f a | i f a -> j
instance
    ( var ~ f (TyVarRep @k ('TyNameRep (GetName k i) i))
    -- Try to unify @a@ with a freshly created @var@.
    , a ~?~ var
    -- If @a@ is equal to @var@ then unification was successful and we just used the fresh id and
    -- so we need to bump it up. Otherwise @var@ was discarded and so the fresh id is still fresh.
    -- Replacing @(===)@ with @(==)@ causes errors at use site, for whatever reason.
    , j ~ If (a === var) (i + 1) i
    ) => TrySpecializeAsVar i j f (a :: k)

-- | First try to specialize the hole using 'TrySpecializeAsVar' and then recurse on the result of
-- that using 'HandleHoles'.
-- @i@ is a fresh id and @j@ is a final one as in 'TrySpecializeAsVar', but since 'HandleHole' can
-- specialize multiple variables, @j@ can be equal to @i + n@ for any @n@ (including @0@).
type HandleHole :: Nat -> Nat -> GHC.Type -> Hole -> GHC.Constraint
class HandleHole i j val hole | i val hole -> j
-- In the Rep context @x@ is attempted to be instantiated as a 'TyVarRep'.
instance
    ( TrySpecializeAsVar i j Id (Id x)  -- The two 'Id's cancel each other.
    , HandleHoles j k val x
    ) => HandleHole i k val (RepHole x)
-- In the Type context @a@ is attempted to be instantiated as a 'TyVarRep' wrapped in @Opaque val@.
instance
    ( TrySpecializeAsVar i j (Opaque val) a
    , HandleHoles j k val a
    ) => HandleHole i k val (TypeHole a)

-- | Call 'HandleHole' over each hole from the list, threading the state (the fresh unique) through
-- the calls.
type HandleHolesGo :: Nat -> Nat -> GHC.Type -> [Hole] -> GHC.Constraint
class HandleHolesGo i j val holes | i val holes -> j
instance i ~ j => HandleHolesGo i j val '[]
instance
      ( HandleHole i j val hole
      , HandleHolesGo j k val holes
      ) => HandleHolesGo i k val (hole ': holes)

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
        ':$$: 'Text "  then go add the instance (you may need a ‘KnownTypeIn’ one too)"
        ':$$: 'Text "  alongside the instance for the built-in type."
        ':$$: 'Text "Otherwise you may need to add a new built-in type"
        ':$$: 'Text "  (provided you're doing something that can be supported in principle)"
        )

-- | Get the holes of @x@ and recurse into them.
type HandleHoles :: forall a. Nat -> Nat -> GHC.Type -> a -> GHC.Constraint
type HandleHoles i j val x =
    -- Here we detect a stuck application of 'ToHoles' and throw 'UnknownTypeError' on it.
    -- See https://blog.csongor.co.uk/report-stuck-families for a detailed description of how
    -- detection of stuck type families works.
    HandleHolesGo i j val (ThrowOnStuckList (UnknownTypeError val x) (ToHoles x))

-- | Specialize each Haskell type variable in @a@ as a type representing a PLC type variable.
-- @i@ is a fresh id and @j@ is a final one as in 'TrySpecializeAsVar', but since 'HandleHole' can
-- specialize multiple variables, @j@ can be equal to @i + n@ for any @n@ (including @0@).
type ElaborateFromTo :: Nat -> Nat -> GHC.Type -> GHC.Type -> GHC.Constraint
type ElaborateFromTo i j val a = HandleHole i j val (TypeHole a)
