-- editorconfig-checker-disable-file
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
-- Required only by 'Permits0' for some reason.
{-# LANGUAGE UndecidableSuperClasses #-}

module Universe.Core
  ( Some (..)
  , ValueOf (..)
  , Contains (..)
  , KnownTypeHead (..)
  , SomeTypeHead
  , Includes
  , knownUniOf
  , someValueOf
  , someValue
  , someValueType
  , Closed (..)
  , Permits
  , EverywhereAll
  , type (<:)
  , GShow (..)
  , gshow
  , GEq (..)
  , defaultEq
  , (:~:) (..)
  -- strictly we don't use this, but this is here
  -- partially so we have a dependency on dependent-sum
  -- directly and so can bound it
  , DSum (..)
  ) where

import Control.DeepSeq
import Control.Monad (guard)
import Data.Dependent.Sum
import Data.GADT.Compare
import Data.GADT.DeepSeq
import Data.GADT.Show
import Data.Hashable
import Data.Kind
import Data.Proxy
import Data.Some.Newtype
import Data.Type.Equality
import Data.Word (Word8)
import PlutusCore.Flat.Decoder (Get)
import Text.Show.Deriving

{- Note [Universes]
A universe is a collection of tags for types. It can be finite like

    data U a where
        UUnit :: U ()
        UInt  :: U Int

(where 'UUnit' is a tag for '()' and 'UInt' is a tag for 'Int') or infinite like

    data U a where
        UBool :: U Bool
        UList :: !(U a) -> U [a]

Here are some values of the latter 'U' / the types that they encode

        UBool               / Bool
        UList UBool         / [Bool]
        UList (UList UBool) / [[Bool]]

'U' being a GADT allows us to package a type from a universe together with a value of that type.
For example,

    Some (ValueOf UBool True) :: Some (ValueOf U)

We say that a type is in a universe whenever there is a tag for that type in the universe.
For example, 'Int' is in 'U', because there exists a tag for 'Int' in 'U' ('UInt').
-}

{- Note [Representing polymorphism]
Constant universes are indexed by fully instantiated Haskell types. A list constructor stores
its element tag directly; a pair constructor stores its two component tags. Bare constructors
belong to 'SomeTypeHead' and can be applied to arbitrary Plutus types through 'TyApp'.
This keeps higher kinds out of runtime constant tags and eliminates kind checking during
constant deserialization. 'KnownTypeAst' reifies constant types for the type checker.
-}

-- | A value of a particular type from a universe.
type ValueOf :: (Type -> Type) -> Type -> Type
data ValueOf uni a = ValueOf !(uni a) !a

-- | A fully instantiated Haskell type in the universe.
type Contains :: (Type -> Type) -> Type -> Constraint
class uni `Contains` a where
  knownUni :: uni a

{- Note [Built-in type heads]
Universes contain fully instantiated Haskell types. Bare constructors belong to the separate
head family: lists of integers have a constant tag, while the list head can be applied to any
Plutus type using TyApp. Heads are ordinary finite data types with structural equality.
-}
type SomeTypeHead :: (Type -> Type) -> Type
data family SomeTypeHead uni

-- | Reify a bare type head. This is independent of constant tags.
type KnownTypeHead :: forall k. (Type -> Type) -> k -> Constraint
class KnownTypeHead uni a where
  knownTypeHead :: SomeTypeHead uni

{- Note [The definition of Includes]
We need to be able to partially apply 'Includes' (required in the definition of '<:' for example),
however if we define 'Includes' as a class alias like that:

    class    Contains uni `Permits` a => uni `Includes` a
    instance Contains uni `Permits` a => uni `Includes` a

we get this extra annoying warning:

    • The constraint ‘Includes uni ()’ matches
        instance forall k (uni :: * -> *) (a :: k).
                 Permits (Contains uni) a =>
                 Includes uni a
      This makes type inference for inner bindings fragile;
        either use MonoLocalBinds, or simplify it using the instance

at the use site, so instead we define 'Includes' as a type alias of one argument (i.e. 'Includes'
has to be immediately applied only to a @uni@ at the use site).
-}

-- See Note [The definition of Includes].
{-| @uni `Includes` a@ reads as \"@a@ is in the @uni@\". @a@ can be of a higher-kind,
in which case membership is required for all its fully instantiated applications. -}
type Includes :: forall k. (Type -> Type) -> k -> Constraint
type Includes uni = Permits (Contains uni)

-- | Same as 'knownUni', but receives a @proxy@.
knownUniOf :: uni `Contains` a => proxy a -> uni a
knownUniOf _ = knownUni

-- | Wrap a value into @Some (ValueOf uni)@, given its explicit type tag.
someValueOf :: forall a uni. uni a -> a -> Some (ValueOf uni)
someValueOf uni = Some . ValueOf uni

-- | Wrap a value into @Some (ValueOf uni)@, provided its type is in the universe.
someValue :: forall a uni. uni `Contains` a => a -> Some (ValueOf uni)
someValue = someValueOf knownUni

someValueType :: Some (ValueOf uni) -> Some uni
someValueType (Some (ValueOf tag _)) = Some tag

{-| A universe is 'Closed', if it's known how to constrain every type from the universe and
every type can be encoded to / decoded from a sequence of integer tags.
The universe doesn't have to be finite and providing support for infinite universes is the
reason why we encode a type as a sequence of integer tags as opposed to a single integer tag.
For example, given

>   data U a where
>       UList :: !(U a) -> U [a]
>       UInt  :: U Int

@UList (UList UInt)@ can be encoded to @[0,0,1]@ where @0@ and @1@ are the integer tags of the
@UList@ and @UInt@ constructors, respectively. -}
class
  ( Eq (SomeTypeHead uni)
  , Ord (SomeTypeHead uni)
  , Show (SomeTypeHead uni)
  , NFData (SomeTypeHead uni)
  , Hashable (SomeTypeHead uni)
  ) =>
  Closed uni
  where
  -- | Stable encoding of a bare head.
  encodeTypeHead :: SomeTypeHead uni -> Word8

  decodeTypeHead :: Word8 -> Maybe (SomeTypeHead uni)

  -- | A constrant for \"@constr a@ holds for any @a@ from @uni@\".
  type Everywhere uni (constr :: Type -> Constraint) :: Constraint

  -- | Encode a type as a sequence of byte-sized tags.
  encodeUni :: uni a -> [Word8]

  -- | Decode a complete type tag from its Flat encoding.
  decodeUni :: Get (Some uni)

  {-| Bring a @constr a@ instance in scope, provided @a@ is a type from the universe and
  @constr@ holds for any type from the universe. -}
  bring :: uni `Everywhere` constr => proxy constr -> uni a -> (constr a => r) -> r

-- It's not possible to return a @forall@ from a type family, let alone compute a proper
-- quantified context, hence the boilerplate and a finite number of supported cases.

type Permits0 :: (Type -> Constraint) -> Type -> Constraint
class constr x => constr `Permits0` x
instance constr x => constr `Permits0` x

type Permits1 :: (Type -> Constraint) -> (Type -> Type) -> Constraint
class (forall a. constr a => constr (f a)) => constr `Permits1` f
instance (forall a. constr a => constr (f a)) => constr `Permits1` f

type Permits2 :: (Type -> Constraint) -> (Type -> Type -> Type) -> Constraint
class (forall a b. (constr a, constr b) => constr (f a b)) => constr `Permits2` f
instance (forall a b. (constr a, constr b) => constr (f a b)) => constr `Permits2` f

type Permits3 :: (Type -> Constraint) -> (Type -> Type -> Type -> Type) -> Constraint
class (forall a b c. (constr a, constr b, constr c) => constr (f a b c)) => constr `Permits3` f
instance (forall a b c. (constr a, constr b, constr c) => constr (f a b c)) => constr `Permits3` f

-- I tried defining 'Permits' as a class but that didn't have the right inference properties
-- (i.e. I was getting errors in existing code). That probably requires bidirectional instances
-- to work, but who cares given that the type family version works alright and can even be
-- partially applied (the kind has to be provided immediately though, but that's fine).
{-| @constr `Permits` f@ elaborates to one of
-
    constr f
    forall a. constr a => constr (f a)
    forall a b. (constr a, constr b) => constr (f a b)
    forall a b c. (constr a, constr b, constr c) => constr (f a b c)

depending on the kind of @f@. This allows us to say things like

   ( constr `Permits` Integer
   , constr `Permits` []
   , constr `Permits` (,)
   )

and thus constraint every type from the universe (including polymorphic ones) to satisfy
@constr@, which is how we provide an implementation of 'Everywhere' for universes with
polymorphic types.

'Permits' is an open type family, so you can provide type instances for @f@s expecting
more type arguments than 3 if you need that.

Note that, say, @constr `Permits` []@ elaborates to

    forall a. constr a => constr [a]

and for certain type classes that does not make sense (e.g. the 'Generic' instance of @[]@
does not require the type of elements to be 'Generic'), however it's not a problem because
we use 'Permit' to constrain the whole universe and so we know that arguments of polymorphic
built-in types are builtins themselves are hence do satisfy the constraint and the fact that
these constraints on arguments do not get used in the polymorphic case only means that they
get ignored. -}
type Permits :: forall k. (Type -> Constraint) -> k -> Constraint
type family Permits constr

type instance Permits @Type constr = Permits0 constr
type instance Permits @(Type -> Type) constr = Permits1 constr
type instance Permits @(Type -> Type -> Type) constr = Permits2 constr
type instance Permits @(Type -> Type -> Type -> Type) constr = Permits3 constr

-- We can't use @All (Everywhere uni) constrs@, because 'Everywhere' is an associated type family
-- and can't be partially applied, so we have to inline the definition here.
type EverywhereAll :: (Type -> Type) -> [Type -> Constraint] -> Constraint
type family uni `EverywhereAll` constrs where
  uni `EverywhereAll` '[] = ()
  uni `EverywhereAll` (constr ': constrs) = (uni `Everywhere` constr, uni `EverywhereAll` constrs)

-- | A constraint for \"@uni1@ is a subuniverse of @uni2@\".
type uni1 <: uni2 = uni1 `Everywhere` Includes uni2

{- Note [The G, the Tag and the Auto]
The existing 'Some' wrapper uses the generalized classes 'GShow', 'GEq', 'GCompare'
and 'GNFData' to obtain ordinary 'Show', 'Eq', 'Ord' and 'NFData' instances.
Universes implement these classes directly; there is no separate wrapper for type tags.

Tag encodings provide stable hashing and serialization. Values use 'ValueOf', which
pairs a tag with a value of its type. Its instances use 'bring' to obtain the relevant
instance for that value. Hashing includes both the encoded tag and the value;
serialization writes the tag followed by the value. Each universe supplies its own
Flat instance for existential tags, while values share the 'Some (ValueOf uni)' instance.

For derived instances, the internal 'AG' wrapper translates ordinary methods to their
G counterparts. For example, 'makeLift' calls 'lift', so wrapping a tag in 'AG' makes
that call use 'glift'. The same approach lets 'makeShowsPrec' use 'gshowsPrec', retaining
the derived handling of precedence and parentheses.
-}

-- WARNING: DO NOT EXPORT THIS, IT HAS AN UNSOUND 'Lift' INSTANCE USED FOR INTERNAL PURPOSES.
{-| A wrapper that allows to provide an instance for a non-general class (e.g. 'Lift' or 'Show')
for any @f@ implementing a general class (e.g. 'GLift' or 'GShow'). -}
newtype AG f a = AG (f a)

$(return []) -- Stage restriction, see https://gitlab.haskell.org/ghc/ghc/issues/9813

-------------------- 'Show' / 'GShow'

instance GShow f => Show (AG f a) where
  showsPrec pr (AG a) = gshowsPrec pr a

instance (GShow uni, Closed uni, uni `Everywhere` Show) => GShow (ValueOf uni) where
  gshowsPrec = showsPrec
instance (GShow uni, Closed uni, uni `Everywhere` Show) => Show (ValueOf uni a) where
  showsPrec pr (ValueOf uni x) =
    bring (Proxy @Show) uni $ ($(makeShowsPrec ''ValueOf)) pr (ValueOf (AG uni) x)

-------------------- 'Eq' / 'GEq'

instance (GEq uni, Closed uni, uni `Everywhere` Eq) => GEq (ValueOf uni) where
  ValueOf uni1 x1 `geq` ValueOf uni2 x2 = do
    Refl <- uni1 `geq` uni2
    guard $ bring (Proxy @Eq) uni1 (x1 == x2)
    Just Refl

instance (GEq uni, Closed uni, uni `Everywhere` Eq) => Eq (ValueOf uni a) where
  (==) = defaultEq

-------------------- 'Compare' / 'GCompare'

instance
  (GCompare uni, Closed uni, uni `Everywhere` Ord, uni `Everywhere` Eq)
  => GCompare (ValueOf uni)
  where
  ValueOf uni1 x1 `gcompare` ValueOf uni2 x2 =
    case uni1 `gcompare` uni2 of
      GLT -> GLT
      GGT -> GGT
      GEQ ->
        bring (Proxy @Ord) uni1 $ case x1 `compare` x2 of
          EQ -> GEQ
          LT -> GLT
          GT -> GGT

-- We need the 'Eq' constraint in order for @Ord (ValueOf uni a)@ to imply @Eq (ValueOf uni a)@.
instance
  (GCompare uni, Closed uni, uni `Everywhere` Ord, uni `Everywhere` Eq)
  => Ord (ValueOf uni a)
  where
  compare = defaultCompare

-------------------- 'NFData'

instance (Closed uni, uni `Everywhere` NFData) => GNFData (ValueOf uni) where
  grnf (ValueOf uni x) = bring (Proxy @NFData) uni $ rnf x

instance (Closed uni, uni `Everywhere` NFData) => NFData (ValueOf uni a) where
  rnf = grnf

instance
  (Closed uni, GEq uni, uni `Everywhere` Eq, uni `Everywhere` Hashable)
  => Hashable (ValueOf uni a)
  where
  hashWithSalt salt (ValueOf uni x) =
    bring (Proxy @Hashable) uni $ hashWithSalt salt (encodeUni uni, x)

instance
  (Closed uni, GEq uni, uni `Everywhere` Eq, uni `Everywhere` Hashable)
  => Hashable (Some (ValueOf uni))
  where
  hashWithSalt salt (Some s) = hashWithSalt salt s
