{-# LANGUAGE DataKinds #-}
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

{-# LANGUAGE QuantifiedConstraints #-}

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
    type uni `Everywhere` (constr :: * -> Constraint) :: Constraint
    bring :: uni `Everywhere` constr => proxy constr -> uni a -> (constr a => r) -> r

-- class HoldsAt f uni constr where
--     bringAt :: Proxy f -> proxy constr -> uni a -> (constr (f a) => r) -> r

-- instance HoldsAt [] ExampleUni Eq where
--     bringAt _ _     ExampleUniInt        r = r
--     bringAt p proxy (ExampleUniList uni) r = bringAt p proxy uni r

-- instance Closed ExampleUni where
--     type ExampleUni `Everywhere` constr = (constr Int, HoldsAt [] ExampleUni constr)
--     bring _     ExampleUniInt        r = r
--     bring proxy (ExampleUniList uni) r = bringAt (Proxy @[]) proxy uni r



-- instance (uni `Includes` a, Closed uni, uni `Everywhere` constr) => Proto uni constr a where
--     protoBring pConstr pEl r = bring pConstr (knownUni `asProxyTypeOf` pEl) r



{-

data Deep (constr :: * -> Constraint)

type family FromStrategy strat :: * -> Constraint
type instance FromStrategy (Deep constr) = constr

class Reflect uni where
    reflect :: uni a -> (uni `Includes` a => c) -> c

class Proto (uni :: * -> *) strat a where
    protoBring
        :: constr ~ FromStrategy strat
        => proxy1 constr -> proxy2 (uni a) -> (constr a => c) -> c
-}

{-
newtype Deep a = Deep
    { unDeep :: a
    }

instance ( uni `Includes` a
         , Closed uni
         , uni `Everywhere` constr
         , forall a. constr a => constr (Deep [a])
         ) => Proto uni constr (Deep [a]) where
    protoBring pConstr (_ :: proxy2 (uni (Deep [a]))) r = bring pConstr (knownUni @uni @a) r

-}

-- Eq a :=> Eq [a]
-- Eq a => (Eq [a] => r) -> r

class Reflect uni where
    reflect :: uni a -> (uni `Includes` a => c) -> c

class Through (uni :: * -> *) constr a where
    bringStruct :: proxy1 constr -> proxy2 (uni a) -> (constr a => c) -> c

instance ( uni `Includes` a
         , Closed uni, uni `Everywhere` constr
         , forall b. constr b => constr [b]
         ) => Through uni constr [a] where
    bringStruct pConstr (_ :: proxy2 (uni [a])) r = bring pConstr (knownUni @uni @a) r

instance (uni `Includes` a, uni `Includes` b, Closed uni, uni `Everywhere` Eq) =>
            Through uni Eq (a, b) where
    bringStruct pConstr (_ :: proxy2 (uni (a, b))) r =
        bring pConstr (knownUni @uni @a) $ bring pConstr (knownUni @uni @b) r

class (forall a. uni `Includes` a => Through uni constr (f a)) => TypeCons uni constr f
instance (forall a. uni `Includes` a => Through uni constr (f a)) => TypeCons uni constr f



data ExampleUni a where
    ExampleUniInt  :: ExampleUni Int
    ExampleUniList :: ExampleUni a -> ExampleUni [a]

instance Closed ExampleUni where
    type ExampleUni `Everywhere` constr = (constr Int, TypeCons ExampleUni constr [])
    bring _       ExampleUniInt                          r = r
    bring pConstr (ExampleUniList (uni :: ExampleUni a)) r =
        reflect uni $ bringStruct pConstr (Proxy @(ExampleUni [a])) r

instance Reflect ExampleUni where
    reflect ExampleUniInt        r = r
    reflect (ExampleUniList uni) r = reflect uni r

instance ExampleUni `Includes` Int where
    knownUni = ExampleUniInt

instance ExampleUni `Includes` a => ExampleUni `Includes` [a] where
    knownUni = ExampleUniList knownUni

instance GEq ExampleUni where
    ExampleUniInt       `geq` ExampleUniInt       = Just Refl
    ExampleUniList uni1 `geq` ExampleUniList uni2 = do
        Refl <- uni1 `geq` uni2
        Just Refl
    _                   `geq` _ = Nothing

instance GShow ExampleUni where
    gshow _ = "uni"

test1 = SomeOf ExampleUniInt 5 == SomeOf ExampleUniInt 6
test2 = show $ SomeOf (ExampleUniList ExampleUniInt) [5, 5] -- == SomeOf (ExampleUniList ExampleUniInt) [5, 5]

-- type EqUni uni = (GEq uni, Closed uni, uni `Everywhere` Eq)

-- ExampleUni [a]

-- class (forall a. ExampleUni `Includes` a => constr [a]) => ExampleUniListConstr constr
-- instance (forall a. ExampleUni `Includes` a => constr [a]) => ExampleUniListConstr constr

-- -- uni a -> (uni `Includes` a => c) -> c

-- instance Closed ExampleUni where
--     type ExampleUni `Everywhere` constr = (constr Int, ExampleUniListConstr constr)
--     bring _     ExampleUniInt  r = r
-- --     bring proxy ExampleUniList r = bring proxy knownUni r



instance Closed uni => Closed (Extend b uni) where
    type Extend b uni `Everywhere` constr = (constr b, uni `Everywhere` constr)
    bring _     Extension      r = r
    bring proxy (Original uni) r = bring proxy uni r

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

instance (GShow uni, Closed uni, uni `Everywhere` Show) => Show (SomeOf uni) where
    show (SomeOf uni x) =
        intercalate " "
            [ "SomeOf"
            , parens $ gshow uni
            , parens $ bring (Proxy @Show) uni (show x)
            ]

instance GShow uni => GShow (Extend b uni) where
    gshow Extension      = "Extension"
    gshow (Original uni) = gshow uni

instance GShow uni => Pretty (Some uni) where
    pretty (Some uni) = pretty $ gshow uni

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
