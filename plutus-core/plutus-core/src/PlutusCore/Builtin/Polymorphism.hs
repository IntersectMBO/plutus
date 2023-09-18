-- editorconfig-checker-disable-file
{-# LANGUAGE ConstraintKinds          #-}
{-# LANGUAGE DataKinds                #-}
{-# LANGUAGE FlexibleInstances        #-}
{-# LANGUAGE MultiParamTypeClasses    #-}
{-# LANGUAGE PolyKinds                #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeFamilies             #-}
{-# LANGUAGE TypeOperators            #-}
{-# LANGUAGE UndecidableInstances     #-}

module PlutusCore.Builtin.Polymorphism
    ( Opaque (..)
    , SomeConstant (..)
    , TyNameRep (..)
    , TyVarRep
    , TyAppRep
    , TyForallRep
    , BuiltinHead
    , ElaborateBuiltin
    , AllElaboratedArgs
    , AllBuiltinArgs
    ) where

import PlutusPrelude

import PlutusCore.Builtin.HasConstant
import PlutusCore.Core
import PlutusCore.Evaluation.Machine.ExMemoryUsage

import Data.Kind qualified as GHC
import GHC.Ix
import GHC.TypeLits
import Universe

{- Note [Motivation for polymorphic built-in functions]
We need to support polymorphism for built-in functions for these reasons:

1. @ifThenElse@ for 'Bool' (being a built-in type rather than a Scott-encoded one) has to be
polymorphic as its type signature is

    ifThenElse : all a. Bool -> a -> a -> a

Previously we had 'Bool' as a Scott-encoded type, but this required plenty of supporting machinery,
because unlifting (aka Scott-decoding) a PLC 'Bool' to a Haskell 'Bool' is quite a non-trivial
thing. We got rid of it and now we have to pay for that by supporting polymorphic built-in functions
(but we added that support long ago anyway, 'cause it was easy to do).

2. we have polymorphic built-in types such as lists and pairs and we need polymorphic built-in
functions to handle them
-}

{- Note [Implementation of polymorphic built-in functions]
Encoding polymorphism in an AST in an intrinsically-typed manner is not a pleasant thing to do in
Haskell. It's not impossible, see "Embedding F", Sam Lindley:

    http://homepages.inf.ed.ac.uk/slindley/papers/embedding-f.pdf

but it's extremely heavy and we don't need it, hence we avoid it.

Instead, we pass type tags at runtime and ensure that a built-in function can be applied to an
argument by checking equality of the type tag that we get by looking at the signature of the
denotation of the builtin and the type tag that we get at runtime as a part of the argument.

But we don't need to check equality of type tags when the denotation of the builtin is polymorphic
over the type of its argument, because then we can simply pass the AST directly through the builtin
without ever extracting anything from it.

We do still need to type check such a builtin in Plutus though, hence we introduce a @newtype@
wrapper for attaching a Plutus type to the argument, so that the Plutus type checker can pick it up.

In particular, an opaque value whose type is a PLC type variable `a_0` has the following type on
the Haskell side:

    Opaque val (TyVarRep ('TyNameRep "a" 0))

where that last argument is a direct counterpart of the term-level

    TyVar () (TyName (Name "a" 0))

@Opaque val rep@ can be used for passing any @val@ through the builtin application machinery,
not just one whose type is a bound variable. For example, you can define a new data type

    data NatRep

provide a 'KnownTypeAst' instance for it and define a (rather pointless) builtin like
@idNat : nat -> nat@.

It's also possible to bind a type variable of a higher-kind, say, @f :: * -> *@ and make a builtin
with the following signature:

    idFInteger : all (f :: * -> *). f integer -> f integer

where the type application is handled with 'TyAppRep'. Note that the latter is defined as a
@data family@:

    data family TyAppRep (fun :: dom -> cod) (arg :: dom) :: cod

We do that because a @data family@ can return a poly-kinded argument, which allows us to get an
intrinsically-kinded representation of PLC types. For example, an opaque @term@ whose type is an
application of a type variable @f@ to a type variable @a@ is represented like this:

    Opaque val (TyAppRep (TyVarRep ('TyNameRep "f" 0)) (TyVarRep ('TyNameRep "a" 1 :: TyNameRep *)))

Note the @TyNameRep *@ kind annotation. It tells us three things:

1. a type-level name has a kind associated with it. The reason for that is that we use names in
binders (for example, in the universal quantifier) and as variables and kinds are important in
both these cases due to us having an intrinsically-kinded representation of types, so it's
convenient to annotate type-level names with kinds. Another reason is that we do not attempt to do
any kind of static analysis on reflected type variables and associating kinds with them allows us
to catch errors like "two variables with equal names and uniques, but different kinds" earlier
2. the kind is not stored as an argument to the @TyNameRep@ constructor. Instead it's stored as
an index of the data type. The point of this is that if we stored the kind as an argument, we'd
have to provide it manually, but since the representation is intrinsically-kinded there's no point
in doing so as GHC can infer all the kinds itself
3. ... apart from cases where they're inherently ambiguous, like in the case above. If we don't
specify the kind of the @a_1@ type variable, then there's no way GHC could infer it as the variable
is passed as an argument to another variable with an unspecified kind (@f_0@)
4. finally, an opaque value can only be of a type of kind @*@. You can't construct a value whose
type is of some other kind. That's why we don't need to annotate the @f_0@ type variable: the domain
is inferred from the kind of the argument (where it's explicitly specified via @TyNameRep *@) and
the codomain is inferred from the fact that the whole type is passed to 'Opaque' and so it has to be
of kind @*@

It would be nice if we didn't need to define that @*Rep@ stuff at the type level just to demote it
to the term level via a type class, but this hasn't been investigated yet. A plausible way would be
to ditch 'KnownTypeAst' (but keep 'ReadKnownIn' and 'MakeKnownIn') and provide PLC types
manually. But that doesn't seem to give rise to a terribly nice API. And we'd lose all the static
guarantees, which is not a big deal, but losing the automatic inference of type schemes would suck,
given that it's quite handy.

Representing constructors as poly-kinded data families and handling those with open type families
and/or type classes is a way of solving the expression problem for indexed data types at the type
level, if you are into these things.

See Note [Elaboration of polymorphism] for how this machinery is used in practice.
-}

-- See Note [Motivation for polymorphic built-in functions].
-- See Note [Implementation of polymorphic built-in functions].
-- | The AST of a value with a Plutus type attached to it. The type is for the Plutus type checker
-- to look at. 'Opaque' can appear in the type of the denotation of a builtin.
newtype Opaque val (rep :: GHC.Type) = Opaque
    { unOpaque :: val
    } deriving newtype (HasConstant, ExMemoryUsage)
-- Try not to add instances for this data type, so that we can throw more 'NoConstraintsErrMsg'
-- kind of type errors.

type instance UniOf (Opaque val rep) = UniOf val

-- | For unlifting from the 'Constant' constructor when the stored value is of a monomorphic
-- built-in type
--
-- The @rep@ parameter specifies how the type looks on the PLC side (i.e. just like with
-- @Opaque val rep@).
newtype SomeConstant uni (rep :: GHC.Type) = SomeConstant
    { unSomeConstant :: Some (ValueOf uni)
    }

deriving newtype instance (Everywhere uni ExMemoryUsage, Closed uni)
    => ExMemoryUsage (SomeConstant uni rep)

type instance UniOf (SomeConstant uni rep) = uni

instance HasConstant (SomeConstant uni rep) where
    asConstant = coerceArg pure
    {-# INLINE asConstant #-}

    fromConstant = coerce
    {-# INLINE fromConstant #-}

-- | Representation of a type variable: its name and unique and an implicit kind.
data TyNameRep (kind :: GHC.Type) = TyNameRep Symbol Nat

-- | Representation of an intrinsically-kinded type variable: a name.
data family TyVarRep (name :: TyNameRep kind) :: kind

-- | Representation of an intrinsically-kinded type application: a function and an argument.
data family TyAppRep (fun :: dom -> cod) (arg :: dom) :: cod

-- | Representation of of an intrinsically-kinded universal quantifier: a bound name and a body.
data family TyForallRep (name :: TyNameRep kind) (a :: GHC.Type) :: GHC.Type

-- | For annotating an uninstantiated built-in type, so that it gets handled by the right instance
-- or type family.
type BuiltinHead :: forall a. a -> a
data family BuiltinHead x

-- | Take an iterated application of a built-in type and elaborate every function application
-- inside of it to 'TyAppRep' and annotate the head with 'BuiltinHead'.
--
-- The idea is that we don't need to process built-in types manually if we simply add some
-- annotations for instance resolution to look for. Think what we'd have to do manually for, say,
-- 'ToHoles': traverse the spine of the application and collect all the holes into a list, which is
-- troubling, because type applications are left-nested and lists are right-nested, so we'd have to
-- use accumulators or an explicit 'Reverse' type family. And then we also have 'KnownTypeAst' and
-- 'ToBinds', so handling built-in types in a special way for each of those would be a hassle,
-- especially given the fact that type-level Haskell is not exactly good at computing things.
-- With the 'ElaborateBuiltin' approach we get 'KnownTypeAst', 'ToHoles' and 'ToBinds' for free.
--
-- We make this an open type family, so that elaboration is customizable for each universe.
type ElaborateBuiltin :: forall a. (GHC.Type -> GHC.Type) -> a -> a
type family ElaborateBuiltin uni x

-- | Take a constraint and use it to constrain every argument of a possibly 0-ary elaborated
-- application of a built-in type.
type AllElaboratedArgs :: forall a. (GHC.Type -> GHC.Constraint) -> a -> GHC.Constraint
type family AllElaboratedArgs constr x where
    AllElaboratedArgs constr (f `TyAppRep` x) = (constr x, AllElaboratedArgs constr f)
    AllElaboratedArgs _      (BuiltinHead _)  = ()

-- | Take a constraint and use it to constrain every argument of a possibly 0-ary application of a
-- built-in type.
type AllBuiltinArgs
        :: forall a. (GHC.Type -> GHC.Type) -> (GHC.Type -> GHC.Constraint) -> a -> GHC.Constraint
type AllBuiltinArgs uni constr x = AllElaboratedArgs constr (ElaborateBuiltin uni x)

-- Custom type errors to guide the programmer adding a new built-in function.

-- We don't have @Unsatisfiable@ yet (https://github.com/ghc-proposals/ghc-proposals/pull/433).
-- | To be used when there's a 'TypeError' in the context. The condition is not checked as there's
-- no way we could do that.
underTypeError :: void
underTypeError = error "Panic: a 'TypeError' was bypassed"

type NoStandalonePolymorphicDataErrMsg =
    'Text "An unwrapped built-in type constructor can't be applied to a type variable" ':$$:
    'Text "Are you trying to define a polymorphic built-in function over a polymorphic type?" ':$$:
    'Text "In that case you need to wrap all polymorphic built-in types applied to type" ':$$:
    'Text " variables with either ‘SomeConstant’ or ‘Opaque’ depending on whether its the" ':$$:
    'Text " type of an argument or the type of the result, respectively"

instance TypeError NoStandalonePolymorphicDataErrMsg => uni `Contains` TyVarRep where
    knownUni = underTypeError

type NoConstraintsErrMsg =
    'Text "Built-in functions are not allowed to have constraints" ':$$:
    'Text "To fix this error instantiate all constrained type variables"

instance TypeError NoConstraintsErrMsg => Eq (Opaque val rep) where
    (==) = underTypeError

instance TypeError NoConstraintsErrMsg => Ord (Opaque val rep) where
    compare = underTypeError

instance TypeError NoConstraintsErrMsg => Num (Opaque val rep) where
    (+)         = underTypeError
    (*)         = underTypeError
    abs         = underTypeError
    signum      = underTypeError
    fromInteger = underTypeError
    negate      = underTypeError

instance TypeError NoConstraintsErrMsg => Enum (Opaque val rep) where
    toEnum   = underTypeError
    fromEnum = underTypeError

instance TypeError NoConstraintsErrMsg => Real (Opaque val rep) where
    toRational = underTypeError

instance TypeError NoConstraintsErrMsg => Integral (Opaque val rep) where
    quotRem   = underTypeError
    divMod    = underTypeError
    toInteger = underTypeError

instance TypeError NoConstraintsErrMsg => Bounded (Opaque val rep) where
    minBound = underTypeError
    maxBound = underTypeError

instance TypeError NoConstraintsErrMsg => Ix (Opaque val rep) where
    range   = underTypeError
    index   = underTypeError
    inRange = underTypeError

instance TypeError NoConstraintsErrMsg => Semigroup (Opaque val rep) where
    (<>) = underTypeError

instance TypeError NoConstraintsErrMsg => Monoid (Opaque val rep) where
    mempty = underTypeError
