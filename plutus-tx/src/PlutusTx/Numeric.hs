{-# LANGUAGE ConstraintKinds        #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}
{-# OPTIONS_GHC -Wno-orphans #-}
module PlutusTx.Numeric (AdditiveSemigroup (..), AdditiveMonoid (..), AdditiveGroup (..), negate, Additive (..), MultiplicativeSemigroup (..), MultiplicativeMonoid (..), Multiplicative (..), Semiring, Ring, Module (..)) where

import           Data.Semigroup     (Product (..), Sum (..))
import           PlutusTx.Builtins
import           PlutusTx.Monoid
import           PlutusTx.Semigroup
import           Prelude            hiding (Functor (..), Monoid (..), Num (..), Semigroup (..))

infixl 7 *
infixl 6 +, -

-- | A 'Semigroup' that it is sensible to describe using addition.
class AdditiveSemigroup a where
    (+) :: a -> a -> a

-- | A 'Monoid' that it is sensible to describe using addition and zero.
class AdditiveSemigroup a => AdditiveMonoid a where
    zero :: a

-- | A 'Group' that it is sensible to describe using addition, zero, and subtraction.
class AdditiveMonoid a => AdditiveGroup a where
    (-) :: a -> a -> a

{-# NOINLINE negate #-}
negate :: AdditiveGroup a => a -> a
negate x = zero - x

-- | A newtype wrapper to derive 'Additive' classes via.
newtype Additive a = Additive a

instance Semigroup a => AdditiveSemigroup (Additive a) where
    {-# NOINLINE (+) #-}
    Additive x + Additive y = Additive (x <> y)

instance Monoid a => AdditiveMonoid (Additive a) where
    {-# NOINLINE zero #-}
    zero = Additive mempty

instance Group a => AdditiveGroup (Additive a) where
    {-# NOINLINE (-) #-}
    Additive x - Additive y = Additive (x `gsub` y)

-- | A 'Semigroup' that it is sensible to describe using multiplication.
class MultiplicativeSemigroup a where
    (*) :: a -> a -> a

-- | A 'Semigroup' that it is sensible to describe using multiplication and one.
class MultiplicativeSemigroup a => MultiplicativeMonoid a where
    one :: a

-- TODO: multiplicative group? I haven't added any since for e.g. integers division
-- is not a proper inverse, so it's of limited use.

-- | A newtype wrapper to derive 'Multiplicative' classes via.
newtype Multiplicative a = Multiplicative a

instance Semigroup a => MultiplicativeSemigroup (Multiplicative a) where
    {-# NOINLINE (*) #-}
    Multiplicative x * Multiplicative y = Multiplicative (x <> y)

instance Monoid a => MultiplicativeMonoid (Multiplicative a) where
    {-# NOINLINE one #-}
    one = Multiplicative mempty

-- | A semiring.
type Semiring a = (AdditiveMonoid a, MultiplicativeMonoid a)
-- | A ring.
type Ring a = (AdditiveGroup a, MultiplicativeMonoid a)

instance AdditiveSemigroup Integer where
    {-# NOINLINE (+) #-}
    (+) = addInteger

instance AdditiveMonoid Integer where
    {-# NOINLINE zero #-}
    zero = 0

instance AdditiveGroup Integer where
    {-# NOINLINE (-) #-}
    (-) = subtractInteger

instance MultiplicativeSemigroup Integer where
    {-# NOINLINE (*) #-}
    (*) = multiplyInteger

instance MultiplicativeMonoid Integer where
    {-# NOINLINE one #-}
    one = 1

instance AdditiveSemigroup Bool where
    {-# INLINABLE (+) #-}
    (+) = (||)

instance AdditiveMonoid Bool where
    {-# INLINABLE zero #-}
    zero = False

instance MultiplicativeSemigroup Bool where
    {-# INLINABLE (*) #-}
    (*) = (&&)

instance MultiplicativeMonoid Bool where
    {-# INLINABLE one #-}
    one = True

-- | A module, with a type of scalars which can be used to scale the values.
class (Ring s, AdditiveGroup v) => Module s v | v -> s where
    scale :: s -> v -> v

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
