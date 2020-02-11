{-# LANGUAGE ConstraintKinds           #-}
{-# LANGUAGE DataKinds                 #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE GADTs                     #-}
{-# LANGUAGE KindSignatures            #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE RankNTypes                #-}
{-# LANGUAGE TypeApplications          #-}
{-# LANGUAGE TypeFamilies              #-}
{-# LANGUAGE TypeOperators             #-}
{-# LANGUAGE UndecidableInstances      #-}
{-# LANGUAGE QuantifiedConstraints     #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE TemplateHaskell #-}

module Language.PlutusCore.Universe.Core
    ( Some (..)
    , SomeOf (..)
    , someValue
    , Includes (..)
    , Closed (..)
    , type (<:)
    , knownUniOf
    , bringApply
    , GEq (..)
    , (:~:) (..)
    , GShow (..)
    , gshow
    , GLift (..)
    ) where

import           Control.DeepSeq
import           Data.GADT.Compare
import           Data.GADT.Show
import           Data.Hashable
import           Data.List
import           Data.Proxy
import           Data.Text.Prettyprint.Doc (Pretty (..))
import           GHC.Exts
import           Language.Haskell.TH.Syntax
import           Language.Haskell.TH.Lift

data Some f = forall a. Some (f a)
data SomeOf f = forall a. SomeOf (f a) a

-- We probably want to use that together with `fastsum`.
class uni `Includes` a where
    knownUni :: uni a

knownUniOf :: uni `Includes` a => proxy a -> uni a
knownUniOf _ = knownUni

someValue :: forall a uni. uni `Includes` a => a -> SomeOf uni
someValue = SomeOf knownUni

class Closed uni where
    type Everywhere uni (constr :: * -> Constraint) :: Constraint
    tagOf :: uni a -> Int
    uniAt :: Int -> Maybe (Some uni)
    bring :: uni `Everywhere` constr => proxy constr -> uni a -> (constr a => r) -> r

type uni1 <: uni2 = uni1 `Everywhere` Includes uni2

bringApply
    :: (Closed uni, uni `Everywhere` constr)
    => Proxy constr -> (forall a. constr a => a -> r) -> SomeOf uni -> r
bringApply proxy f (SomeOf uni x) = bring proxy uni $ f x

parens :: String -> String
parens str = "(" ++ str ++ ")"

instance GShow uni => Show (Some uni) where
   show (Some uni) = "Some " ++ parens (gshow uni)

instance (GShow uni, Closed uni, uni `Everywhere` Show) => Show (SomeOf uni) where
    show (SomeOf uni x) =
        intercalate " "
            [ "SomeOf"
            , parens $ gshow uni
            , parens $ bring (Proxy @Show) uni (show x)
            ]

instance GShow uni => Pretty (Some uni) where
    pretty (Some uni) = pretty $ gshow uni

instance (Closed uni, uni `Everywhere` Pretty) => Pretty (SomeOf uni) where
    pretty = bringApply (Proxy @Pretty) pretty

instance GEq uni => Eq (Some uni) where
    Some uni1 == Some uni2 = uni1 `defaultEq` uni2

instance (GEq uni, Closed uni, uni `Everywhere` Eq) => Eq (SomeOf uni) where
    SomeOf uni1 x1 == SomeOf uni2 x2 =
        case uni1 `geq` uni2 of
            Nothing   -> False
            Just Refl -> bring (Proxy @Eq) uni1 (x1 == x2)

-- We could use 'NFData1' here, but we don't really need it for our particular case.
instance NFData (Some f) where
    rnf (Some a) = a `seq` ()

-- | 'GLift' to 'Lift' is what 'GShow' to 'Show'.
class GLift f where
    glift :: f a -> Q Exp
    default glift :: Lift (f a) => f a -> Q Exp
    glift = lift

-- | A wrapper that allows to provide a 'Lift' instance for any @uni@ implementing 'GLift'.
newtype AGLift uni a = AGLift
    { unAGLift :: uni a
    }

instance GLift uni => Lift (AGLift uni a) where
    lift = glift . unAGLift

newtype SomeAGLift uni = SomeAGLift
    { unSomeAGLift :: Some (AGLift uni)
    }

$(return [])
instance GLift uni => Lift (SomeAGLift uni) where
    lift = $(makeLift ''Some) . unSomeAGLift

-- >>> :set -XGADTs
-- >>> :set -XStandaloneDeriving
-- >>> :set -XTemplateHaskell
-- >>> data U a where UInt :: U Int; UBool :: U Bool
-- >>> deriving instance Show (U a)
-- >>> instance GShow U where gshowsPrec = showsPrec
-- >>> deriving instance Lift (U a)
-- >>> instance GLift U
-- >>> $(lift $ Some UInt)
-- Some (UInt)
deriving via SomeAGLift uni instance GLift uni => Lift (Some uni)

instance Closed uni => Hashable (Some uni) where
    hashWithSalt salt (Some uni) = hashWithSalt salt $ tagOf uni

instance (Closed uni, uni `Everywhere` NFData) => NFData (SomeOf uni) where
    rnf = bringApply (Proxy @NFData) rnf

instance (GLift uni, Closed uni, uni `Everywhere` Lift) => Lift (SomeOf uni) where
    -- TODO: FIXME.
    lift = undefined

instance (Closed uni, uni `Everywhere` Hashable) => Hashable (SomeOf uni) where
    hashWithSalt salt (SomeOf uni x) =
        bring (Proxy @Hashable) uni $ hashWithSalt salt (Some uni, x)
