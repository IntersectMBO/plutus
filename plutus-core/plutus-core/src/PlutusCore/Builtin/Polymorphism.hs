{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}

module PlutusCore.Builtin.Polymorphism
    ( Opaque (..)
    , SomeConstant (..)
    , TyNameRep (..)
    , TyVarRep
    , TyAppRep
    , TyForallRep
    ) where

import PlutusCore.Builtin.HasConstant
import PlutusCore.Core
import PlutusCore.Pretty

import Control.Applicative
import Control.Monad
import Control.Monad.IO.Class
import Data.Bifoldable
import Data.Bifunctor
import Data.Bitraversable
import Data.Kind qualified as GHC (Type)
import GHC.Ix
import GHC.TypeLits
import Universe

{- Note [Motivation for polymorphic built-in functions]
We need to support polymorphism for built-in functions for these reasons:

1. @ifThenElse@ for 'Bool' (being a built-in type rather than a Scott-encoded one) has to be
   polymorphic as its type signature is

       ifThenElse : all a. Bool -> a -> a -> a

   Previously we had 'Bool' as a Scott-encoded type, but this required plenty of supporting machinery,
   because unlifting (aka Scott-decoding) a PLC 'Bool' into a Haskell 'Bool' is quite a non-trivial
   thing, see https://github.com/input-output-hk/plutus/blob/e222466e6d46bbca9f76243bb496b3c88ed02ca1/language-plutus-core/src/PlutusCore.Builtin/Typed.hs#L165-L252

   Now that we got rid of all this complexity we have to pay for that by supporting polymorphic
   built-in functions (but we added that support long ago anyway, 'cause it was easy to do).

2. we may want to add efficient polymorphic built-in types like @IntMap@ or @Vector@ and most functions
   defined over them are polymorphic as well
-}

-- See Note [Motivation for polymorphic built-in functions].
-- See Note [Implementation of polymorphic built-in functions].
-- See Note [Pattern matching on built-in types].
-- | The denotation of a term whose PLC type is encoded in @rep@ (for example a type variable or
-- an application of a type variable). I.e. the denotation of such a term is the term itself.
-- This is because we have parametricity in Haskell, so we can't inspect a value whose
-- type is, say, a bound variable, so we never need to convert such a term from Plutus Core to
-- Haskell and back and instead can keep it intact.
newtype Opaque val (rep :: GHC.Type) = Opaque
    { unOpaque :: val
    } deriving newtype (Pretty, HasConstant)

type instance UniOf (Opaque val rep) = UniOf val

-- | For unlifting from the 'Constant' constructor when the stored value is of a monomorphic
-- built-in type
--
-- The @rep@ parameter specifies how the type looks on the PLC side (i.e. just like with
-- @Opaque val rep@).
newtype SomeConstant uni (rep :: GHC.Type) = SomeConstant
    { unSomeConstant :: Some (ValueOf uni)
    }

{- Note [Implementation of polymorphic built-in functions]
Encoding polymorphism in an AST in an intrinsically-typed manner is not a pleasant thing to do in Haskell.
It's not impossible, see "Embedding F", Sam Lindley: http://homepages.inf.ed.ac.uk/slindley/papers/embedding-f.pdf
But we'd rather avoid such heavy techniques.

Fortunately, there is a simple trick: we have parametricity in Haskell, so a function that is
polymorphic in its argument can't inspect that argument in any way and so we never actually need to
convert such an argument from PLC to Haskell just to convert it back later without ever inspecting
the value. Instead we can keep the argument intact and apply the Haskell function directly to
the PLC AST representing some value.

E.g. Having a built-in function with the following signature:
(TODO: we can't have that, figure out a way to make this example actually work while being as
clear as it currently is)

    reverse : all a. [a] -> [a]

that maps to Haskell's

    reverse :: forall a. [a] -> [a]

evaluation of

    PLC.reverse {bool} (cons true (cons false nil))

proceeds as follows:

      PLC.reverse {bool} (cons true (cons false nil))
    ~ makeKnown (Haskell.reverse (readKnown (cons true (cons false nil))))
    ~ makeKnown (Haskell.reverse [Opaque true, Opaque false])
    ~ makeKnown [Opaque false, Opaque true]
    ~ EvaluationSuccess (cons false (cons true nil))

Note how we use the 'Opaque' wrapper in order to unlift a PLC term as an opaque Haskell value
using 'readKnown' and then lift the term back using 'makeKnown' without ever inspecting the term.

An opaque PLC @term@ whose type is a PLC type variable `a_0` has the following type on the Haskell
side:

    Opaque val (TyVarRep ('TyNameRep "a" 0))

where that last argument is a direct counterpart of the term-level

    TyVar () (TyName (Name "a" 0))

@Opaque val rep@ can be used for passing any @term@ through the builtin application machinery,
not just one whose type is a bound variable. For example, you can define a new data type

    data NatRep

provide a 'KnownTypeAst' instance for it (mapping a @Proxy NatRep@ to the actual type of natural
numbers in PLC) and define a (rather pointless) builtin like @idNat : nat -> nat@.

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
4. finally, an opaque term can only be of a type of kind @*@. You can't construct a term whose type
is of some other kind. That's why we don't need to annotate the @f_0@ type variable: the domain is
inferred from the kind of the argument (where it's explicitly specified via @TyNameRep *@) and the
codomain is inferred from the fact that the whole type is passed to 'Opaque' and so it has to be
of kind @*@

It would be nice if we didn't need to define that @*Rep@ stuff at the type level just to demote it
to the term level via a type class, but this hasn't been investigated yet. A plausible way would be
to ditch 'KnownTypeAst' (but keep 'KnownType') and provide PLC types manually. But that doesn't seem
to give rise to a terribly nice API. And we'd lose all the static guarantees, which is not a big
deal, but losing the automatic inference of type schemes would suck, given that it's quite handy.

Representing contructors as poly-kinded data families and handling those with open type families
and/or type classes is a way of solving the expression problem for indexed data types at the type
level, if you are into these things.
-}

-- | Representation of a type variable: its name and unique and an implicit kind.
data TyNameRep (kind :: GHC.Type) = TyNameRep Symbol Nat

-- | Representation of an intrinsically-kinded type variable: a name.
data family TyVarRep (name :: TyNameRep kind) :: kind

-- | Representation of an intrinsically-kinded type application: a function and an argument.
data family TyAppRep (fun :: dom -> cod) (arg :: dom) :: cod

-- | Representation of of an intrinsically-kinded universal quantifier: a bound name and a body.
data family TyForallRep (name :: TyNameRep kind) (a :: GHC.Type) :: GHC.Type

-- Custom type errors to guide the programmer adding a new built-in function.
-- We cover a lot of cases here, but some are missing, for example we do not attempt to detect
-- higher-kinded type variables, which means that if your function returns an @m a@ we can neither
-- instantiate @m@ (which is impossible anyway: it could be 'EvaluationResult' or 'Emitter'
-- or else), nor report that higher-kinded type variables are not allowed and suggest
-- to instantiate such variables manually. In general, we do not attempt to look inside type
-- applications (as it's a rather hard thing to do) and so a type variable inside, say, a list
-- does not get instantiated, hence the custom type error does not get triggered (as it's only
-- triggered for instantiated type variables) and the user gets a standard unhelpful GHC error.

-- We don't have @Unsatisfiable@ yet (https://github.com/ghc-proposals/ghc-proposals/pull/433).
-- | To be used when there's a 'TypeError' in the context. The condition is not checked as there's
-- no way we could do that.
underTypeError :: void
underTypeError = error "Panic: a 'TypeError' was bypassed"

type NoStandalonePolymorphicDataErrMsg =
    'Text "Plutus type variables can't directly appear inside built-in types" ':$$:
    'Text "Are you trying to define a polymorphic built-in function over a polymorphic type?" ':$$:
    'Text "In that case you need to wrap all polymorphic built-in types having type variables" ':<>:
    'Text " in them with either ‘SomeConstant’ or ‘Opaque’ depending on whether its the type" ':<>:
    'Text " of an argument or the type of the result, respectively"

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

type NoRegularlyAppliedHkVarsMsg =
    'Text "Built-in functions are not allowed to have higher-kinded type variables" ':<>:
    'Text " applied via regular type application" ':$$:
    'Text "To fix this error instantiate all higher-kinded type variables"

instance TypeError NoRegularlyAppliedHkVarsMsg => Functor (Opaque val) where
    fmap = underTypeError

instance TypeError NoRegularlyAppliedHkVarsMsg => Foldable (Opaque val) where
    foldMap = underTypeError

instance TypeError NoRegularlyAppliedHkVarsMsg => Traversable (Opaque val) where
    traverse = underTypeError

instance TypeError NoRegularlyAppliedHkVarsMsg => Applicative (Opaque val) where
    pure = underTypeError
    (<*>) = underTypeError

instance TypeError NoRegularlyAppliedHkVarsMsg => Alternative (Opaque val) where
    empty = underTypeError
    (<|>) = underTypeError

instance TypeError NoRegularlyAppliedHkVarsMsg => Monad (Opaque val) where
    (>>=) = underTypeError

instance TypeError NoRegularlyAppliedHkVarsMsg => MonadIO (Opaque val) where
    liftIO = underTypeError

instance TypeError NoRegularlyAppliedHkVarsMsg => MonadPlus (Opaque val) where
    mzero = underTypeError
    mplus = underTypeError

instance TypeError NoRegularlyAppliedHkVarsMsg => MonadFail (Opaque val) where
    fail = underTypeError

instance TypeError NoRegularlyAppliedHkVarsMsg => Bifunctor Opaque where
    bimap = underTypeError

instance TypeError NoRegularlyAppliedHkVarsMsg => Bifoldable Opaque where
    bifoldMap = underTypeError

instance TypeError NoRegularlyAppliedHkVarsMsg => Bitraversable Opaque where
    bitraverse = underTypeError
