{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE DefaultSignatures     #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# LANGUAGE TemplateHaskell       #-}

module Language.PlutusCore.Universe.Core
    ( Some (..)
    , In (..)
    , Of (..)
    , SomeIn
    , SomeOf
    , someValue
    , Includes (..)
    , Closed (..)
    , type (<:)
    , knownUniOf
    , GShow (..)
    , gshow
    , GEq (..)
    , (:~:) (..)
    , GLift (..)
    ) where

import           Control.DeepSeq
import           Control.Monad
import           Data.GADT.Compare
import           Data.GADT.Show
import           Data.Hashable
import           Data.Proxy
import           Data.Text.Prettyprint.Doc (Pretty (..))
import           GHC.Exts
import           Language.Haskell.TH.Lift
import           Language.Haskell.TH.Syntax
import           Text.Show.Deriving

{- Note [Universes]
A universe is a collection of types. It can be finite like

    data U a where
        UUnit :: U ()
        UInt  :: U Int

or infinite like

    data U a where
        UBool :: U Bool
        UList :: !(U a) -> U [a]

Here are some values of the latter 'U' / the types that they encode

        UBool               / Bool
        UList UBool         / [Bool]
        UList (UList UBool) / [[Bool]]

'U' being a GADT allows to package a type from a universe together with a value of that type.
For example,

    Some (Of UBool True) :: Some (Of U)
-}

-- | Existential quantification as a data type.
data Some f = forall a. Some (f a)

-- | A particular type from a universe.
newtype In uni a = In (uni a)

-- | A value of a particular type from a universe.
data Of uni a = Of (uni a) a

-- | Some type from a universe.
type SomeIn uni = Some (In uni)

-- | A value of some type from a universe.
type SomeOf uni = Some (Of uni)

-- We probably want to use that together with `fastsum`.
-- | A constraint for \"@a@ is in @uni@\".
class uni `Includes` a where
    knownUni :: uni a

-- | Same as 'knownUni', but receives a @proxy@.
knownUniOf :: uni `Includes` a => proxy a -> uni a
knownUniOf _ = knownUni

-- | Wrap a value into @SomeOf uni@, provided its type is in the universe.
someValue :: forall a uni. uni `Includes` a => a -> SomeOf uni
someValue = Some . Of knownUni

-- | A universe is 'Closed', if it's known how to constrain every type from the universe
-- (the universe doesn't have to be finite for that).
class Closed uni where
    -- | A constrant for \"@constr a@ holds for any @a@ from @uni@\".
    type Everywhere uni (constr :: * -> Constraint) :: Constraint

    -- | Get the 'Int' tag of a type from @uni@. The opposite of 'uniAt'.
    tagOf :: uni a -> Int

    -- | Get the universe at a tag. The opposite of 'tagOf'.
    uniAt :: Int -> Maybe (SomeIn uni)

    -- | Bring a @constr a@ instance in scope, provided @a@ is a type from the universe and
    -- @constr@ holds for any type from the universe.
    bring :: uni `Everywhere` constr => proxy constr -> uni a -> (constr a => r) -> r

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
that has @Some f@ somewhere inside it and forces you to use a standalong deriving declaration for
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

    instance Closed uni => Hashable (In uni a) where
        hashWithSalt salt (In uni) = hashWithSalt salt $ tagOf uni

    instance Closed uni => Hashable (Some (In uni)) where
        hashWithSalt salt (Some s) = hashWithSalt salt s

where

    class Closed uni where
        tagOf :: uni a -> Int
        <...>

So as long as for each type of a universe you know its integer tag, you can hash any type from
the universe via its tag. 'Serialise' is handled in a similar way.

The 'Hashable' type class is also interesting in that we do not provide a generic instance for
any @Some f@. This is because @f@ can be anything of kind @* -> *@ and we only have 'tagOf' for
universes. In order to stress that the @f@ in this instance has to be a universe we use
the 'In' wrapper:

    instance Closed uni => Hashable (Some (In uni)) where

This allows us to hash a type from a universe and a value of a type from a universe in different ways.
The latter instance looks like this:

    instance (Closed uni, uni `Everywhere` Hashable) => Hashable (Of uni a) where
        hashWithSalt salt (Of uni x) =
            bring (Proxy @Hashable) uni $ hashWithSalt salt (Some (In uni), x)

    instance (Closed uni, uni `Everywhere` Hashable) => Hashable (Some (Of uni)) where
        hashWithSalt salt (Some s) = hashWithSalt salt s

Here we hash an 'Of' value as a pair of a type from a universe and a value of that type.

Another type class for which a generic @Some f@ instance doesn't make sense is 'NFData'.
For universes we define

    instance NFData (In uni a) where
        rnf (In uni) = uni `seq` ()

    instance NFData (Some (In uni)) where
        rnf (Some s) = rnf s

i.e. to fully force a type from a universe it's enough to just call `seq` over it, because
universes are mostly non-recursive data types and even in the recursive case it makes sense to
require the universe to be constructed strictly, i.e.

    data U a where
        UList :: !(U a) -> U [a]
        <...>

this saves us from defining the G version of 'NFData'.

But for handling 'NFData' we could also just get the tag of a type and force it instead.
However integer tags don't seem to play well with recursive universes: how would you handle
the 'U' example from the above? So we might consider switching to some other encoding of tags,
hence it's good to be able not to rely on them.

3. the Auto:

When we can manually provide an instance for a type class, the two previous approaches work nicely.
But for a type class like 'Lift' we really want to use the deriving mechanism in order not to mess
with the hairy internal representation ('Exp' and stuff). But 'deriveLift' (and 'makeLift') calls
'lift' under the hood while we want it to call 'glift'. So we define a newtype wrapper ('AG') that
implements 'Lift' in terms of 'GLift', insert the 'AG' constructor in the right place and invoke
'makeLift' which calls 'lift' on 'AG' internally, so the 'lift' gets elaborated to 'glift'
as we want it to.

And even though we can manually write 'Show' instances, they're handled in the same automated way below,
just because the derived instances handle precedence (and thus insert parentheses in right places)
out of the box.

We should be able to use the same strategy for every type class @X@ when a @makeX@ function
(analogous to 'makeLift') is available.
-}

-- | A wrapper that allows to provide a 'Lift' instance for any @f@ implementing 'GLift'.
newtype AG f a = AG (f a)

$(return [])  -- Staged restriction.

-------------------- 'Show' / 'GShow'

instance GShow f => Show (AG f a) where
    showsPrec pr (AG a) = gshowsPrec pr a

instance GShow f => Show (Some f) where
    showsPrec pr (Some a) = ($(makeShowsPrec ''Some)) pr (Some (AG a))

instance GShow uni => GShow (In uni) where gshowsPrec = showsPrec
instance GShow uni => Show (In uni a) where
    showsPrec pr (In uni) = ($(makeShowsPrec ''In)) pr (In (AG uni))

instance (GShow uni, Closed uni, uni `Everywhere` Show) => GShow (Of uni) where gshowsPrec = showsPrec
instance (GShow uni, Closed uni, uni `Everywhere` Show) => Show (Of uni a) where
    showsPrec pr (Of uni x) = bring (Proxy @Show) uni $ ($(makeShowsPrec ''Of)) pr (Of (AG uni) x)

-------------------- 'Pretty'

instance GShow uni => Pretty (In uni a) where
    pretty (In uni) = pretty $ gshow uni

instance (Closed uni, uni `Everywhere` Pretty) => Pretty (Of uni a) where
    pretty (Of uni x) = bring (Proxy @Pretty) uni $ pretty x

instance GShow uni => Pretty (Some (In uni)) where
    pretty (Some s) = pretty s

instance (Closed uni, uni `Everywhere` Pretty) => Pretty (Some (Of uni)) where
    pretty (Some s) = pretty s

-------------------- 'Eq' / 'GEq'

instance GEq f => Eq (Some f) where
    Some a1 == Some a2 = a1 `defaultEq` a2

deriving newtype instance GEq uni => GEq (In uni)

instance (GEq uni, Closed uni, uni `Everywhere` Eq) => GEq (Of uni) where
    Of uni1 x1 `geq` Of uni2 x2 = do
        Refl <- uni1 `geq` uni2
        guard $ bring (Proxy @Eq) uni1 (x1 == x2)
        Just Refl

instance GEq uni => Eq (In uni a) where
    a1 == a2 = a1 `defaultEq` a2

instance (GEq uni, Closed uni, uni `Everywhere` Eq) => Eq (Of uni a) where
    a1 == a2 = a1 `defaultEq` a2

-------------------- 'NFData'

instance NFData (In uni a) where
    rnf (In uni) = uni `seq` ()

instance (Closed uni, uni `Everywhere` NFData) => NFData (Of uni a) where
    rnf (Of uni x) = bring (Proxy @NFData) uni $ rnf x

instance NFData (Some (In uni)) where
    rnf (Some s) = rnf s

instance (Closed uni, uni `Everywhere` NFData) => NFData (Some (Of uni)) where
    rnf (Some s) = rnf s

-------------------- 'Hashable'

instance Closed uni => Hashable (In uni a) where
    hashWithSalt salt (In uni) = hashWithSalt salt $ tagOf uni

instance (Closed uni, uni `Everywhere` Hashable) => Hashable (Of uni a) where
    hashWithSalt salt (Of uni x) =
        bring (Proxy @Hashable) uni $ hashWithSalt salt (Some (In uni), x)

instance Closed uni => Hashable (Some (In uni)) where
    hashWithSalt salt (Some s) = hashWithSalt salt s

instance (Closed uni, uni `Everywhere` Hashable) => Hashable (Some (Of uni)) where
    hashWithSalt salt (Some s) = hashWithSalt salt s

-------------------- 'Lift'

-- | 'GLift' to 'Lift' is what 'GShow' to 'Show'.
class GLift f where
    glift :: f a -> Q Exp
    default glift :: Lift (f a) => f a -> Q Exp
    glift = lift

instance GLift f => Lift (AG f a) where
    lift (AG a) = glift a

-- See Note [Lift, the black sheep].
-- >>> :set -XGADTs
-- >>> :set -XStandaloneDeriving
-- >>> :set -XTemplateHaskell
-- >>> :set -XTypeFamilies
-- >>> data U a where UInt :: U Int; UBool :: U Bool
-- >>> deriving instance Show (U a)
-- >>> deriving instance Lift (U a)
-- >>> instance GShow U where gshowsPrec = showsPrec
-- >>> instance GLift U
-- >>> instance Closed U where type Everywhere U constr = (constr Int, constr Bool); tagOf = undefined; uniAt = undefined; bring _ UInt = id; bring _ UBool = id
-- >>> $(lift $ Some UBool)
-- Some UBool
-- >>> $(lift $ Some (In UInt))
-- Some (In UInt)
-- >>> $(lift $ Some (Of UBool True))
-- Some (Of UBool True)
instance GLift f => Lift (Some f) where
    lift (Some a) = ($(makeLift ''Some)) (Some (AG a))

instance GLift uni => GLift (In uni)
instance GLift uni => Lift (In uni a) where
    lift (In uni) = ($(makeLift ''In)) (In (AG uni))

instance (GLift uni, Closed uni, uni `Everywhere` Lift) => GLift (Of uni)
instance (GLift uni, Closed uni, uni `Everywhere` Lift) => Lift (Of uni a) where
    lift (Of uni x) = bring (Proxy @Lift) uni $ ($(makeLift ''Of)) (Of (AG uni) x)
