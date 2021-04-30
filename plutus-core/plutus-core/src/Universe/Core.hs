{-# LANGUAGE ConstraintKinds          #-}
{-# LANGUAGE DataKinds                #-}
{-# LANGUAGE FlexibleInstances        #-}
{-# LANGUAGE GADTs                    #-}
{-# LANGUAGE MultiParamTypeClasses    #-}
{-# LANGUAGE PolyKinds                #-}
{-# LANGUAGE QuantifiedConstraints    #-}
{-# LANGUAGE RankNTypes               #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TemplateHaskell          #-}
{-# LANGUAGE TypeApplications         #-}
{-# LANGUAGE TypeFamilies             #-}
{-# LANGUAGE TypeOperators            #-}
{-# LANGUAGE UndecidableInstances     #-}
-- Required only by 'Permits0' for some reason.
{-# LANGUAGE UndecidableSuperClasses  #-}

module Universe.Core
    ( Some (..)
    , SomeTypeIn (..)
    , Kinded (..)
    , ValueOf (..)
    , someValueOf
    , someValue
    , Contains (..)
    , Includes
    , DecodeUniM (..)
    , Closed (..)
    , decodeKindedUni
    , peelUniTag
    , Permits
    , EverywhereAll
    , type (<:)
    , knownUniOf
    , GShow (..)
    , gshow
    , GEq (..)
    , deriveGEq
    , (:~:) (..)
    , T
    ) where

import           Control.Applicative
import           Control.DeepSeq
import           Control.Monad
import           Control.Monad.Trans.State.Strict
import           Data.GADT.Compare
import           Data.GADT.Compare.TH
import           Data.GADT.Show
import           Data.Hashable
import           Data.Kind
import           Data.Proxy
import           Text.Show.Deriving
import           Type.Reflection

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

type T :: forall k. k -> Type
data T a

-- | Existential quantification as a data type.
type Some :: forall a. (a -> Type) -> Type
data Some f = forall x. Some !(f x)

-- | A particular type from a universe.
type SomeTypeIn :: (Type -> Type) -> Type
data SomeTypeIn uni = forall k (a :: k). SomeTypeIn !(uni (T a))

data Kinded uni ta where
    Kinded :: Typeable k => !(uni (T a)) -> Kinded uni (T (a :: k))

-- | A value of a particular type from a universe.
type ValueOf :: (Type -> Type) -> Type -> Type
data ValueOf uni a = ValueOf !(uni (T a)) !a

-- | A class for enumerating types and fully instantiated type formers that @uni@ contains.
-- For example, a particular @ExampleUni@ may have monomorphic types in it:
--
--     instance ExampleUni `Contains` Integer where <...>
--     instance ExampleUni `Contains` Bool    where <...>
--
-- as well as polymorphic ones:
--
--     instance ExampleUni `Contains` a => ExampleUni `Contains` [a] where <...>
--     instance (ExampleUni `Contains` a, ExampleUni `Contains` b) => ExampleUni `Contains` (a, b) where <...>
--
-- Note that when used as a constraint of a function 'Contains' does not allow you to directly
-- express things like \"@uni@ has the @Integer@, @Bool@ and @[]@ types and type formers\",
-- because @[]@ is not fully instantiated. So you can only say \"@uni@ has @Integer@, @Bool@,
-- @[Integer]@, @[Bool]@, @[[Integer]]@, @[[Bool]]@ etc\" and such manual enumeration is annoying,
-- so we'd really like to be able to say that @uni@ has lists of arbitrary built-in types
-- (including lists of lists etc). 'Contains' does not allow that, but 'Includes' does.
-- For example, in the body of the following definition:
--
--     foo :: (uni `Includes` Integer, uni `Includes` Bool, uni `Includes` []) => <...>
--     foo = <...>
--
-- you can make use of the fact that @uni@ has lists of arbitrary included types (integers,
-- booleans and lists).
--
-- Hence don't use 'Contains' in constraints, opt for the more flexible 'Includes'.
--
-- 'Includes' is defined in terms of 'Contains', so you only need to provide a 'Contains' instance
-- per type from the universe and you'll get 'Includes' for free.
type Contains :: forall k. (Type -> Type) -> k -> Constraint
class uni `Contains` a where
    knownUni :: uni (T a)

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
has to be immediately applied to a @uni@ at the use site).
-}

-- See Note [The definition of Includes].
-- | @uni `Includes` a@ reads as \"@a@ is in the @uni@\". @a@ can be of a higher-kind,
-- see the docs of 'Contains' on why you might want that.
type Includes :: forall k. (Type -> Type) -> k -> Constraint
type Includes uni = Permits (Contains uni)

-- | Same as 'knownUni', but receives a @proxy@.
knownUniOf :: uni `Contains` a => proxy a -> uni (T a)
knownUniOf _ = knownUni

-- | Wrap a value into @Some (ValueOf uni)@, given its explicit type tag.
someValueOf :: forall a uni. uni (T a) -> a -> Some (ValueOf uni)
someValueOf uni = Some . ValueOf uni

-- | Wrap a value into @Some (ValueOf uni)@, provided its type is in the universe.
someValue :: forall a uni. uni `Includes` a => a -> Some (ValueOf uni)
someValue = someValueOf knownUni

-- | A monad to decode types from a universe in.
newtype DecodeUniM a = DecodeUniM
    { unDecodeUniM :: StateT [Int] Maybe a
    } deriving newtype (Functor, Applicative, Alternative, Monad, MonadFail)

runDecodeUniM :: [Int] -> DecodeUniM a -> Maybe (a, [Int])
runDecodeUniM is (DecodeUniM a) = runStateT a is

-- | A universe is 'Closed', if it's known how to constrain every type from the universe.
-- The universe doesn't have to be finite and providing support for infinite universes is the
-- reason why we encode a type as a sequence of integer tags as opposed to a single integer tag.
-- For example, given
--
-- >   data U a where
-- >       UList :: !(U a) -> U [a]
-- >       UInt  :: U Int
--
-- @UList (UList UInt)@ can be encoded to @[0,0,1]@ where @0@ and @1@ are the integer tags of the
-- @UList@ and @UInt@ constructors, respectively.
class Closed uni where
    -- | A constrant for \"@constr a@ holds for any @a@ from @uni@\".
    type Everywhere uni (constr :: Type -> Constraint) :: Constraint

    -- | Encode a type as a sequence of 'Int' tags.
    -- The opposite of 'decodeUni'.
    encodeUni :: uni a -> [Int]

    -- | Decode a type and feed it to the continuation.
    withDecodedUni :: (forall k (a :: k). Typeable k => uni (T a) -> DecodeUniM r) -> DecodeUniM r

    -- | Bring a @constr a@ instance in scope, provided @a@ is a type from the universe and
    -- @constr@ holds for any type from the universe.
    bring :: uni `Everywhere` constr => proxy constr -> uni (T a) -> (constr a => r) -> r

-- | Decode a type from a sequence of 'Int' tags.
-- The opposite of 'encodeUni' (modulo invalid input).
decodeKindedUni :: Closed uni => [Int] -> Maybe (SomeTypeIn (Kinded uni))
decodeKindedUni is = do
    (x, []) <- runDecodeUniM is $ withDecodedUni $ pure . SomeTypeIn . Kinded
    pure x

-- >>> runDecodeUniM [1,2,3] peelUniTag
-- Just (1,[2,3])
-- >>> runDecodeUniM [] peelUniTag
-- Nothing
peelUniTag :: DecodeUniM Int
peelUniTag = DecodeUniM $ do
    i:is <- get
    i <$ put is

-- It's not possible to return a @forall@ from a type family, let alone compute a proper
-- quantified context, hence the boilerplate and a finite number of supported cases.

type Permits0 :: (Type -> Constraint) -> Type -> Constraint
class    constr x => constr `Permits0` x
instance constr x => constr `Permits0` x

type Permits1 :: (Type -> Constraint) -> (Type -> Type) -> Constraint
class    (forall a. constr a => constr (f a)) => constr `Permits1` f
instance (forall a. constr a => constr (f a)) => constr `Permits1` f

type Permits2 :: (Type -> Constraint) -> (Type -> Type -> Type) -> Constraint
class    (forall a b. (constr a, constr b) => constr (f a b)) => constr `Permits2` f
instance (forall a b. (constr a, constr b) => constr (f a b)) => constr `Permits2` f

type Permits3 :: (Type -> Constraint) -> (Type -> Type -> Type -> Type) -> Constraint
class    (forall a b c. (constr a, constr b, constr c) => constr (f a b c)) => constr `Permits3` f
instance (forall a b c. (constr a, constr b, constr c) => constr (f a b c)) => constr `Permits3` f

-- I tried defining 'Permits' as a class but that didn't have the right inference properties
-- (i.e. I was getting errors in existing code). That probably requires bidirectional instances
-- to work, but who cares given that the type family version works alright and can even be
-- partially applied (the kind has to be provided immediately though, but that's fine).
-- | @constr `Permits` f@ elaborates to one of
--
--     constr f
--     forall a. constr a => constr (f a)
--     forall a b. (constr a, constr b) => constr (f a b)
--     forall a b c. (constr a, constr b, constr c) => constr (f a b c)
--
-- depending on the kind of @f@. This allows us to say things like
--
--    ( constr `Permits` Integer
--    , constr `Permits` []
--    , constr `Permits` (,)
--    )
--
-- and thus constraint every type from the universe (including polymorphic ones) to satisfy
-- @constr@, which is how we provide an implementation of 'Everywhere' for universes with
-- polymorphic types.
--
-- 'Permits' is an open type family, so you can provide type instances for @f@s expecting
-- more types arguments than 3 if you need that.
--
-- Note that, say, @constr `Permits` []@ elaborates to
--
--     forall a. constr a => constr [a]
--
-- and for certain type classes that does not make sense (e.g. the 'Generic' instance of @[]@
-- does not require the type of elements to be 'Generic'), however it's not a problem because
-- we use 'Permit' to constrain the whole universe and so we know that arguments of polymorphic
-- built-in types are builtins themselves are hence do satisfy the constraint and the fact that
-- these constraints on arguments do not get used in the polymorphic case only means that they
-- get ignored.
type Permits :: forall k. (Type -> Constraint) -> k -> Constraint
type family Permits

-- Implicit pattern matching on the kind.
type instance Permits = Permits0
type instance Permits = Permits1
type instance Permits = Permits2
type instance Permits = Permits3

-- We can't use @All (Everywhere uni) constrs@, because 'Everywhere' is an associated type family
-- and can't be partially applied, so we have to inline the definition here.
type EverywhereAll :: (Type -> Type) -> [Type -> Constraint] -> Constraint
type family uni `EverywhereAll` constrs where
    uni `EverywhereAll` '[]                 = ()
    uni `EverywhereAll` (constr ': constrs) = (uni `Everywhere` constr, uni `EverywhereAll` constrs)

-- | A constraint for \"@uni1@ is a subuniverse of @uni2@\".
type uni1 <: uni2 = uni1 `Everywhere` Includes uni2

{- Note [The G, the Tag and the Auto]
Providing instances for

    data Some f = forall a. Some (f a)

is tricky. There are several things to consider here:

1. the G: for some type classes we can provide an instance for @Some f@ for any @f@ generically.
Take for example @Show (Some f)@, we could implement it as

    instance (forall a. Show (f a)) => Show (Some f) where
        show (Some a) = "Some " ++ show a

(with `-XQuantifiedConstraints`). Unfortunately, that breaks @deriving (Show)@ for every data type
that has @Some f@ somewhere inside it and forces you to use a standalone deriving declaration for
each such data type, which is rather annoying, because instance contexts tend to get huge,
so it takes time to come up with them or to remember where to copy them from and they also occupy
a lot of space (text-wise).

Luckily, "Data.GADT.Show" provides

    class GShow t where
        gshowsPrec :: Int -> t a -> ShowS

    gshow :: GShow t => t a -> String

which allows us to define a 'Show' instance for 'Some' as

    instance GShow f => Show (Some f) where
        show (Some a) = "Some " ++ gshow a

so @GShow f@ is basically an encoding of @forall a. Show (f a)@.

2. the Tag: for some type classes we can get away without providing the G version of a type class,
e.g. 'Hashable' is handled like that:

    instance Closed uni => Hashable (TypeIn uni a) where
        hashWithSalt salt (TypeIn uni) = hashWithSalt salt $ encodeUni uni

    instance Closed uni => Hashable (SomeTypeIn uni) where
        hashWithSalt salt (Some s) = hashWithSalt salt s

where

    class Closed uni where
        encodeUni :: uni a -> [Int]
        <...>

So as long as for each type of a universe you know its encoding as a sequence of integer tags,
you can hash any type from the universe via that sequence. 'Serialise' is handled in a similar way.

The 'Hashable' type class is also interesting in that we do not provide a generic instance for
any @Some f@. This is because @f@ can be anything of kind @* -> *@ and we only have 'encodeUni' for
universes. In order to stress that the @f@ in this instance has to be a universe we use
the 'TypeIn' wrapper:

    instance Closed uni => Hashable (SomeTypeIn uni) where

This allows us to hash a type from a universe and a value of a type from a universe in different
ways. The latter instance looks like this:

    instance (Closed uni, uni `Everywhere` Hashable) => Hashable (ValueOf uni a) where
        hashWithSalt salt (ValueOf uni x) =
            bring (Proxy @Hashable) uni $ hashWithSalt salt (SomeTypeIn uni, x)

    instance (Closed uni, uni `Everywhere` Hashable) => Hashable (Some (ValueOf uni)) where
        hashWithSalt salt (Some s) = hashWithSalt salt s

Here we hash a 'ValueOf' value as a pair of a type from a universe and a value of that type.

Another type class for which a generic @Some f@ instance doesn't make sense is 'NFData'.
For universes we define

    instance NFData (TypeIn uni a) where
        rnf (TypeIn uni) = rnf $ encodeUni uni

    instance NFData (SomeTypeIn uni) where
        rnf (Some s) = rnf s

i.e. to fully force a type from a universe it's enough to encode the type as a sequence of integer
tags and fully force that sequence.

3. the Auto:

When we can manually provide an instance for a type class, the two previous approaches work nicely.
But for a type class like 'Lift' we really want to use the deriving mechanism in order not to mess
with the hairy internal representation ('Exp' and stuff). But 'deriveLift' (and 'makeLift') calls
'lift' under the hood while we want it to call 'glift'. So we define a newtype wrapper ('AG') that
implements 'Lift' in terms of 'GLift', insert the 'AG' constructor in the right place and invoke
'makeLift' which calls 'lift' on 'AG' internally, so the 'lift' gets elaborated to 'glift'
as we want it to.

And even though we can manually write 'Show' instances, they're handled in the same automated way
below, just because the derived instances handle precedence (and thus insert parentheses in right
places) out of the box.

We should be able to use the same strategy for every type class @X@ when a @makeX@ function
(analogous to 'makeLift') is available.
-}

-- WARNING: DO NOT EXPORT THIS, IT HAS AN UNSOUND 'Lift' INSTANCE USED FOR INTERNAL PURPOSES.
-- | A wrapper that allows to provide an instance for a non-general class (e.g. `Lift` or 'Show')
-- for any @f@ implementing a general class (e.g. 'GLift' or 'GShow').
newtype AG f a = AG (f a)

$(return [])  -- Stage restriction, see https://gitlab.haskell.org/ghc/ghc/issues/9813

-------------------- 'Show' / 'GShow'

instance GShow f => Show (AG f a) where
    showsPrec pr (AG a) = gshowsPrec pr a

instance GShow f => Show (Some f) where
    showsPrec pr (Some a) = ($(makeShowsPrec ''Some)) pr (Some (AG a))

instance GShow uni => Show (SomeTypeIn uni) where
    showsPrec pr (SomeTypeIn uni) = ($(makeShowsPrec ''SomeTypeIn)) pr (SomeTypeIn (AG uni))

instance GShow uni => Show (Kinded uni ta) where
    showsPrec pr (Kinded uni) = ($(makeShowsPrec ''Kinded)) pr (Kinded (AG uni))

instance GShow uni => GShow (Kinded uni) where gshowsPrec = showsPrec

instance (GShow uni, Closed uni, uni `Everywhere` Show) => GShow (ValueOf uni) where
    gshowsPrec = showsPrec
instance (GShow uni, Closed uni, uni `Everywhere` Show) => Show (ValueOf uni a) where
    showsPrec pr (ValueOf uni x) =
        bring (Proxy @Show) uni $ ($(makeShowsPrec ''ValueOf)) pr (ValueOf (AG uni) x)

-------------------- 'Eq' / 'GEq'

instance GEq f => Eq (Some f) where
    Some a1 == Some a2 = a1 `defaultEq` a2

instance (GEq uni, Closed uni, uni `Everywhere` Eq) => GEq (ValueOf uni) where
    ValueOf uni1 x1 `geq` ValueOf uni2 x2 = do
        Refl <- uni1 `geq` uni2
        guard $ bring (Proxy @Eq) uni1 (x1 == x2)
        Just Refl

instance GEq uni => Eq (SomeTypeIn uni) where
    SomeTypeIn a1 == SomeTypeIn a2 = a1 `defaultEq` a2

instance (GEq uni, Closed uni, uni `Everywhere` Eq) => Eq (ValueOf uni a) where
    (==) = defaultEq

-------------------- 'NFData'

instance Closed uni => NFData (SomeTypeIn uni) where
    rnf (SomeTypeIn uni) = rnf $ encodeUni uni

instance (Closed uni, uni `Everywhere` NFData) => NFData (ValueOf uni a) where
    rnf (ValueOf uni x) = bring (Proxy @NFData) uni $ rnf x

instance (Closed uni, uni `Everywhere` NFData) => NFData (Some (ValueOf uni)) where
    rnf (Some s) = rnf s

-------------------- 'Hashable'

instance Closed uni => Hashable (SomeTypeIn uni) where
    hashWithSalt salt (SomeTypeIn uni) = hashWithSalt salt $ encodeUni uni

instance (Closed uni, uni `Everywhere` Hashable) => Hashable (ValueOf uni a) where
    hashWithSalt salt (ValueOf uni x) =
        bring (Proxy @Hashable) uni $ hashWithSalt salt (SomeTypeIn uni, x)

instance (Closed uni, uni `Everywhere` Hashable) => Hashable (Some (ValueOf uni)) where
    hashWithSalt salt (Some s) = hashWithSalt salt s
