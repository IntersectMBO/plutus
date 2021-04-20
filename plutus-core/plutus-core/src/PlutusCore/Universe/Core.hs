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

module PlutusCore.Universe.Core
    ( Some (..)
    , TypeIn (..)
    , ValueOf (..)
    , someValueOf
    , someValue
    , TypeApp
    , HasUniApply (..)
    , Contains (..)
    , Includes
    , Closed (..)
    , decodeUni
    , peelTag
    , Permits
    , EverywhereAll
    , type (<:)
    , knownUniOf
    , GShow (..)
    , gshow
    , GEq (..)
    , deriveGEq
    , Lift
    , (:~:) (..)
    ) where

import           Control.DeepSeq
import           Control.Monad
import           Control.Monad.Trans.State.Strict
import           Data.GADT.Compare
import           Data.GADT.Compare.TH
import           Data.GADT.Show
import           Data.Hashable
import qualified Data.Kind                        as GHC (Type)
import           Data.Proxy
import           GHC.Exts
import           Language.Haskell.TH.Lift
import           Text.Show.Deriving

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

'U' being a GADT allows to package a type from a universe together with a value of that type.
For example,

    Some (ValueOf UBool True) :: Some (ValueOf U)

We say that a type is in a universe whenever there is a tag for that type in the universe.
For example, 'Int' is in 'U', because there exists a tag for 'Int' in 'U' -- 'UInt'.
-}

-- | Existential quantification as a data type.
data Some f = forall a. Some (f a)

-- | A particular type from a universe.
newtype TypeIn uni a = TypeIn (uni a)

-- | A value of a particular type from a universe.
data ValueOf uni a = ValueOf (uni a) a

-- | A constraint for \"@a@ is in @uni@\".
type Contains :: (GHC.Type -> GHC.Type) -> GHC.Type -> Constraint
class uni `Contains` a where
    knownUni :: uni a

type Includes :: (GHC.Type -> GHC.Type) -> k -> Constraint
type Includes uni = Permits (Contains uni)

-- | Same as 'knownUni', but receives a @proxy@.
knownUniOf :: uni `Includes` a => proxy a -> uni a
knownUniOf _ = knownUni

-- | Wrap a value into @Some (ValueOf uni)@, given its explicit type tag.
someValueOf :: forall a uni. uni a -> a -> Some (ValueOf uni)
someValueOf uni = Some . ValueOf uni

-- | Wrap a value into @Some (ValueOf uni)@, provided its type is in the universe.
someValue :: forall a uni. uni `Includes` a => a -> Some (ValueOf uni)
someValue = someValueOf knownUni

data TypeApp (a :: k)

class HasUniApply uni where
    -- runTypeApp :: uni (TypeApp a) -> uni a
    matchUniRunTypeApp
        :: uni a
        -> r
        -> (uni (TypeApp a) -> r)
        -> r
    matchUniApply
        -- :: uni (TypeApp (fa :: k))
        -- -- -> (k ~ GHC.Type => r)
        -- -> r
        -- -> (forall f a. fa ~ f a => uni (TypeApp (f :: GHC.Type -> k)) -> uni a -> r)
        -- -> r
        :: uni tfa
        -> r
        -> (forall k f a. tfa ~ TypeApp (f a :: k) => uni (TypeApp f) -> uni a -> r)
        -> r

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
    type Everywhere uni (constr :: GHC.Type -> Constraint) :: Constraint

    -- | Encode a type as a sequence of 'Int' tags.
    -- The opposite of 'decodeUni'.
    encodeUni :: uni a -> [Int]

    decodeUniM :: StateT [Int] Maybe (Some (TypeIn uni))

    -- | Bring a @constr a@ instance in scope, provided @a@ is a type from the universe and
    -- @constr@ holds for any type from the universe.
    bring :: uni `Everywhere` constr => proxy constr -> uni a -> (constr a => r) -> r

-- | Decode a type from a sequence of 'Int' tags.
-- The opposite of 'encodeUni' (modulo invalid input).
decodeUni :: Closed uni => [Int] -> Maybe (Some (TypeIn uni))
decodeUni is =
    case runStateT decodeUniM is of
        Just (res, []) -> Just res
        _              -> Nothing

-- >>> runStateT peelTag [1,2,3]
-- Just (1,[2,3])
-- >>> runStateT peelTag []
-- Nothing
peelTag :: StateT [Int] Maybe Int
peelTag = do
    i:is <- get
    i <$ put is

type Permits1 :: (GHC.Type -> Constraint) -> (GHC.Type -> GHC.Type) -> Constraint
class    (forall a. constr a => constr (f a)) => constr `Permits1` f
instance (forall a. constr a => constr (f a)) => constr `Permits1` f

type Permits2 :: (GHC.Type -> Constraint) -> (GHC.Type -> GHC.Type -> GHC.Type) -> Constraint
class    (forall a b. (constr a, constr b) => constr (f a b)) => constr `Permits2` f
instance (forall a b. (constr a, constr b) => constr (f a b)) => constr `Permits2` f

type Permits :: (GHC.Type -> Constraint) -> k -> Constraint
type family Permits constr

type instance Permits constr = constr
type instance Permits constr = Permits1 constr
type instance Permits constr = Permits2 constr

-- We can't use @All (Everywhere uni) constrs@, because 'Everywhere' is an associated type family
-- and can't be partially applied, so we have to inline the definition here.
type family uni `EverywhereAll` (constrs :: [GHC.Type -> Constraint]) :: Constraint where
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

    instance Closed uni => Hashable (Some (TypeIn uni)) where
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

    instance Closed uni => Hashable (Some (TypeIn uni)) where

This allows us to hash a type from a universe and a value of a type from a universe in different
ways. The latter instance looks like this:

    instance (Closed uni, uni `Everywhere` Hashable) => Hashable (ValueOf uni a) where
        hashWithSalt salt (ValueOf uni x) =
            bring (Proxy @Hashable) uni $ hashWithSalt salt (Some (TypeIn uni), x)

    instance (Closed uni, uni `Everywhere` Hashable) => Hashable (Some (ValueOf uni)) where
        hashWithSalt salt (Some s) = hashWithSalt salt s

Here we hash a 'ValueOf' value as a pair of a type from a universe and a value of that type.

Another type class for which a generic @Some f@ instance doesn't make sense is 'NFData'.
For universes we define

    instance NFData (TypeIn uni a) where
        rnf (TypeIn uni) = rnf $ encodeUni uni

    instance NFData (Some (TypeIn uni)) where
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

instance GShow uni => GShow (TypeIn uni) where gshowsPrec = showsPrec

-- If it was possible to combine @stock@ and @via@ that instance could look like
--
--     deriving stock via TypeIn (AG uni) a instance GShow uni => Show (TypeIn uni a)
instance GShow uni => Show (TypeIn uni a) where
    showsPrec pr (TypeIn uni) = ($(makeShowsPrec ''TypeIn)) pr (TypeIn (AG uni))

instance (GShow uni, Closed uni, uni `Everywhere` Show) => GShow (ValueOf uni) where
    gshowsPrec = showsPrec
instance (GShow uni, Closed uni, uni `Everywhere` Show) => Show (ValueOf uni a) where
    showsPrec pr (ValueOf uni x) =
        bring (Proxy @Show) uni $ ($(makeShowsPrec ''ValueOf)) pr (ValueOf (AG uni) x)

-------------------- 'Eq' / 'GEq'

instance GEq f => Eq (Some f) where
    Some a1 == Some a2 = a1 `defaultEq` a2

deriving newtype instance GEq uni => GEq (TypeIn uni)

instance (GEq uni, Closed uni, uni `Everywhere` Eq) => GEq (ValueOf uni) where
    ValueOf uni1 x1 `geq` ValueOf uni2 x2 = do
        Refl <- uni1 `geq` uni2
        guard $ bring (Proxy @Eq) uni1 (x1 == x2)
        Just Refl

instance GEq uni => Eq (TypeIn uni a) where
    (==) = defaultEq

instance (GEq uni, Closed uni, uni `Everywhere` Eq) => Eq (ValueOf uni a) where
    (==) = defaultEq

-------------------- 'NFData'

instance Closed uni => NFData (TypeIn uni a) where
    rnf (TypeIn uni) = rnf $ encodeUni uni

instance (Closed uni, uni `Everywhere` NFData) => NFData (ValueOf uni a) where
    rnf (ValueOf uni x) = bring (Proxy @NFData) uni $ rnf x

instance Closed uni => NFData (Some (TypeIn uni)) where
    rnf (Some s) = rnf s

instance (Closed uni, uni `Everywhere` NFData) => NFData (Some (ValueOf uni)) where
    rnf (Some s) = rnf s

-------------------- 'Hashable'

instance Closed uni => Hashable (TypeIn uni a) where
    hashWithSalt salt (TypeIn uni) = hashWithSalt salt $ encodeUni uni

instance (Closed uni, uni `Everywhere` Hashable) => Hashable (ValueOf uni a) where
    hashWithSalt salt (ValueOf uni x) =
        bring (Proxy @Hashable) uni $ hashWithSalt salt (Some (TypeIn uni), x)

instance Closed uni => Hashable (Some (TypeIn uni)) where
    hashWithSalt salt (Some s) = hashWithSalt salt s

instance (Closed uni, uni `Everywhere` Hashable) => Hashable (Some (ValueOf uni)) where
    hashWithSalt salt (Some s) = hashWithSalt salt s
