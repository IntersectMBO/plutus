{-# LANGUAGE ConstraintKinds        #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}
{-# OPTIONS_GHC -Wno-orphans #-}
module PlutusTx.Numeric
  ( AdditiveSemigroup (..)
  , AdditiveMonoid (..)
  , AdditiveGroup (..)
  , negate
  , Additive (..)
  , MultiplicativeSemigroup (..)
  , MultiplicativeMonoid (..)
  , Multiplicative (..)
  , Semiring
  , Ring
  , Module (..)
  , AdditiveHemigroup (..)
  , monus
  ) where

import           Data.Semigroup         (Product (..), Sum (..))
import           PlutusTx.Monoid
import           PlutusTx.Numeric.Class
import           PlutusTx.Semigroup
import           Prelude                hiding (Functor (..), Monoid (..), Num (..), Semigroup (..), divMod)

-- | A newtype wrapper to derive 'Additive' classes via.
newtype Additive a = Additive a

instance Semigroup a => AdditiveSemigroup (Additive a) where
    {-# INLINABLE (+) #-}
    Additive x + Additive y = Additive (x <> y)

instance Monoid a => AdditiveMonoid (Additive a) where
    {-# INLINABLE zero #-}
    zero = Additive mempty

instance Group a => AdditiveGroup (Additive a) where
    {-# INLINABLE (-) #-}
    Additive x - Additive y = Additive (x `gsub` y)


-- | A newtype wrapper to derive 'Multiplicative' classes via.
newtype Multiplicative a = Multiplicative a

instance Semigroup a => MultiplicativeSemigroup (Multiplicative a) where
    {-# INLINABLE (*) #-}
    Multiplicative x * Multiplicative y = Multiplicative (x <> y)

instance Monoid a => MultiplicativeMonoid (Multiplicative a) where
    {-# INLINABLE one #-}
    one = Multiplicative mempty


instance AdditiveSemigroup a => Semigroup (Sum a) where
    {-# INLINABLE (<>) #-}
    Sum a1 <> Sum a2 = Sum (a1 + a2)

instance AdditiveMonoid a => Monoid (Sum a) where
    {-# INLINABLE mempty #-}
    mempty = Sum zero

instance MultiplicativeSemigroup a => Semigroup (Product a) where
    {-# INLINABLE (<>) #-}
    Product a1 <> Product a2 = Product (a1 * a2)

instance MultiplicativeMonoid a => Monoid (Product a) where
    {-# INLINABLE mempty #-}
    mempty = Product one
