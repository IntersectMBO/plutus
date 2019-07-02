{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE KindSignatures #-}

module Language.PlutusCore.Universe
    ( Some (..)
    , SomeOf (..)
    , KnownUni (..)
    , GShow (..)
    , EqUni
    , bringApply
    ) where

import           GHC.Exts
import           Control.DeepSeq
import           Data.Proxy
import           Data.GADT.Compare
import           Data.List

data Some f = forall a. Some (f a)
data SomeOf f = forall a. SomeOf (f a) a

class KnownUni uni where
    type Everywhere uni (constr :: * -> Constraint) :: Constraint
    bring :: uni `Everywhere` constr => proxy constr -> uni a -> (constr a => r) -> r

bringApply
    :: (KnownUni uni, uni `Everywhere` constr)
    => Proxy constr -> (forall a. constr a => a -> r) -> SomeOf uni -> r
bringApply proxy f (SomeOf uni x) = bring proxy uni $ f x

parens :: String -> String
parens str = "(" ++ str ++ ")"

-- There is 'Show1', but it requires @Show a@, which we don't need and can't get in
-- the @Show (Some uni)@ instance for example.
class GShow f where
    gshow :: f a -> String

instance GShow uni => Show (Some uni) where
   show (Some a) = "Some " ++ parens (gshow a)

instance (GShow uni, KnownUni uni, uni `Everywhere` Show) => Show (SomeOf uni) where
    show (SomeOf uni x) =
        intercalate " "
            [ "SomeOf"
            , parens $ gshow uni
            , parens $ bring (Proxy @Show) uni (show x)
            ]

instance GEq uni => Eq (Some uni) where
    Some uni1 == Some uni2 = uni1 `defaultEq` uni2

type EqUni uni = (GEq uni, KnownUni uni, uni `Everywhere` Eq)

instance EqUni uni => Eq (SomeOf uni) where
    SomeOf uni1 x1 == SomeOf uni2 x2 =
        case uni1 `geq` uni2 of
            Nothing   -> False
            Just Refl -> bring (Proxy @Eq) uni1 (x1 == x2)

-- We could use 'NFData1' here, but we don't really need it for our particular case.
instance NFData (Some f) where
    rnf (Some a) = a `seq` ()

instance (KnownUni uni, uni `Everywhere` NFData) => NFData (SomeOf uni) where
    rnf = bringApply (Proxy @NFData) rnf
