{-# OPTIONS_GHC -fno-warn-orphans #-}

{-# LANGUAGE DefaultSignatures    #-}
{-# LANGUAGE KindSignatures       #-}
{-# LANGUAGE TemplateHaskell      #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module Language.PlutusCore.Universe.Lift
    ( GLift (..)
    ) where

import           Language.PlutusCore.Universe.Core

import           Data.Proxy
import           Language.Haskell.TH.Lift
import           Language.Haskell.TH.Syntax

{- Note [Lift, the black sheep]
Providing instances for

    data Some f = forall a. Some (f a)

is tricky. We handle some type classes with bespoke strategies, e.g. 'Hashable' is handled like that:

    instance Closed uni => Hashable (Some uni) where
        hashWithSalt salt (Some uni) = hashWithSalt salt $ tagOf uni

where

    class Closed uni where
        tagOf :: uni a -> Int
        <...>

'Serialize' is handled in a similar way.

But take @Show (Some f)@, how to implement it? With `-XQuantifiedConstraints`
we can write

    instance (forall a. Show (f a)) => Show (Some f) where
        show (Some a) = "Some " ++ show a

but that breaks @deriving (Show)@ for every data type that has @Some f@ somewhere inside it
and forces you to use a standalong deriving declaration for each such data type, which is
rather annoying, because instance contexts tend to get huge, so it takes time to come up with them
or to remember where to copy them from and they also occupy a lot of space (text-wise).

Luckily, "Data.GADT.Show" provides

    class GShow t where
        gshowsPrec :: Int -> t a -> ShowS

    gshow :: GShow t => t a -> String

which allows us to define a 'Show' instance for 'Some' as

    instance GShow f => Show (Some f) where
        show (Some a) = "Some " ++ gshow a

so @GShow f@ is basically an encoding of @forall a. Show (f a)@.

When we can manually provide an instance for a type class, this works nicely. But for a type class
like 'Lift' we really want to use the deriving mechanism in order not to mess with the hairy
internal representation ('Exp' and stuff). But 'deriveLift' (and 'makeLift') calls 'lift'
under the hood while we want it to call 'glift'. So we define a newtype wrapper ('AGLift') that
implements 'Lift' in terms of 'GLift', insert the 'AGLift' constructor in the right place and invoke
'makeLift' which calls 'lift' on 'AGlift' internally, so the 'lift' gets elaborated to 'glift'
as we want it to.

We should be able to use the same strategy for every type class @X@ when a @makeX@ function
(analogous to 'makeLift') is provided (not aware of any other such class, though).
-}

-- | 'GLift' to 'Lift' is what 'GShow' to 'Show'.
class GLift f where
    glift :: f a -> Q Exp
    default glift :: Lift (f a) => f a -> Q Exp
    glift = lift

-- | A wrapper that allows to provide a 'Lift' instance for any @f@ implementing 'GLift'.
newtype AGLift f a = AGLift (f a)
instance GLift f => Lift (AGLift f a) where
    lift (AGLift a) = glift a

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
-- Some (UBool)
-- >>> $(lift $ Some (In UInt))
-- Some (In (UInt))
-- >>> $(lift $ Some (Of UBool True))
-- Some (Of (UBool) (True))
instance GLift f => Lift (Some f) where
    lift (Some a) = ($(makeLift ''Some)) (Some (AGLift a))

-- See Note [Lift, the black sheep].
instance GLift uni => GLift (In uni)
instance GLift uni => Lift (In uni a) where
    lift (In uni) = ($(makeLift ''In)) (In (AGLift uni))

-- See Note [Lift, the black sheep].
instance (GLift uni, Closed uni, uni `Everywhere` Lift) => GLift (Of uni)
instance (GLift uni, Closed uni, uni `Everywhere` Lift) => Lift (Of uni a) where
    lift (Of uni x) = bring (Proxy @Lift) uni $ ($(makeLift ''Of)) (Of (AGLift uni) x)
