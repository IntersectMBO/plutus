{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE KindSignatures #-}

module Language.PlutusCore.Constant.Universe
    ( Some (..)
    , SomeOf (..)
    , Extend (..)
    , shiftSome
    , shiftSomeOf
    , Includes (..)
    , knownUniOf
    , Closed (..)
    , bringApply
    , GShow (..)
    , EqUni
    ) where

import           Control.DeepSeq
import           Data.Proxy
import           Data.GADT.Compare
import           Data.List
import           GHC.Exts
import           Data.Text.Prettyprint.Doc (Pretty (..))

data Some f = forall a. Some (f a)
data SomeOf f = forall a. SomeOf (f a) a

data Extend b uni a where
    Extension :: Extend b uni b
    Original  :: uni a -> Extend b uni a

instance GEq uni => GEq (Extend b uni) where
    geq Extension       Extension       = Just Refl
    geq (Original uni1) (Original uni2) = geq uni1 uni2
    geq _               _               = Nothing

shiftSome :: Some uni -> Some (Extend b uni)
shiftSome (Some uni) = Some (Original uni)

shiftSomeOf :: SomeOf uni -> SomeOf (Extend b uni)
shiftSomeOf (SomeOf uni x) = SomeOf (Original uni) x

-- We probably want to use that together with `fastsum`.
-- But also allow @Either@ and use type families for computing the index of a type,
-- because we want to extend @uni@ in order to unlift values.
class uni `Includes` a where
    knownUni :: uni a

instance uni `Includes` a => Extend b uni `Includes` a where
    knownUni = Original knownUni

knownUniOf :: uni `Includes` a => proxy a -> uni a
knownUniOf _ = knownUni

class Closed uni where
    type Everywhere uni (constr :: * -> Constraint) :: Constraint
    bring :: uni `Everywhere` constr => proxy constr -> uni a -> (constr a => r) -> r

bringApply
    :: (Closed uni, uni `Everywhere` constr)
    => Proxy constr -> (forall a. constr a => a -> r) -> SomeOf uni -> r
bringApply proxy f (SomeOf uni x) = bring proxy uni $ f x

parens :: String -> String
parens str = "(" ++ str ++ ")"

-- There is 'Show1', but it requires @Show a@, which we don't need and can't satisfy in
-- the @Show (Some uni)@ instance for example.
class GShow f where
    gshow :: f a -> String

instance GShow uni => Show (Some uni) where
   show (Some uni) = "Some " ++ parens (gshow uni)

instance GShow uni => Pretty (Some uni) where
    pretty (Some uni) = pretty $ gshow uni

instance (GShow uni, Closed uni, uni `Everywhere` Show) => Show (SomeOf uni) where
    show (SomeOf uni x) =
        intercalate " "
            [ "SomeOf"
            , parens $ gshow uni
            , parens $ bring (Proxy @Show) uni (show x)
            ]

instance (Closed uni, uni `Everywhere` Pretty) => Pretty (SomeOf uni) where
    pretty = bringApply (Proxy @Pretty) pretty

instance GEq uni => Eq (Some uni) where
    Some uni1 == Some uni2 = uni1 `defaultEq` uni2

type EqUni uni = (GEq uni, Closed uni, uni `Everywhere` Eq)

instance EqUni uni => Eq (SomeOf uni) where
    SomeOf uni1 x1 == SomeOf uni2 x2 =
        case uni1 `geq` uni2 of
            Nothing   -> False
            Just Refl -> bring (Proxy @Eq) uni1 (x1 == x2)

-- We could use 'NFData1' here, but we don't really need it for our particular case.
instance NFData (Some f) where
    rnf (Some a) = a `seq` ()

instance (Closed uni, uni `Everywhere` NFData) => NFData (SomeOf uni) where
    rnf = bringApply (Proxy @NFData) rnf
