module Data.Monoid.Internal(module Data.Monoid.Internal) where
import Control.Applicative
import Control.Error
import Data.Bool
import Data.Bounded
import Data.Coerce
import Data.Eq
import Data.Function
import Data.Functor
import Data.Int
import Data.Integral
import Data.List.NonEmpty_Type
import Data.List_Type
import Data.Maybe_Type
import Data.Num
import Data.Ord
import Data.Records
import Prelude qualified ()
import Primitives
import Text.Show

class Semigroup a => Monoid a where
  mempty :: a
  mappend :: a -> a -> a
  mappend = (<>)
  mconcat :: [a] -> a
  mconcat []     = mempty
  mconcat (a:as) = a <> mconcat as

---------------------

instance (Monoid b) => Monoid (a -> b) where
  mempty _ = mempty

instance (Semigroup b) => Semigroup (a -> b) where
  f <> g = \ x -> f x <> g x

---------------------

newtype Endo a = Endo { appEndo :: a -> a }

instance forall a . Semigroup (Endo a) where
  Endo f <> Endo g = Endo (f . g)

instance forall a . Monoid (Endo a) where
  mempty = Endo id

---------------------

newtype Dual a = Dual { getDual :: a }
  deriving (Bounded, Eq, Ord, Show)

instance forall a . Semigroup a => Semigroup (Dual a) where
  Dual a <> Dual b = Dual (b <> a)

instance forall a . Monoid a => Monoid (Dual a) where
  mempty = Dual mempty

instance Functor Dual where
  fmap f (Dual a) = Dual (f a)

instance Applicative Dual where
  pure = Dual
  Dual f <*> Dual b = Dual (f b)

---------------------

newtype Max a = Max { getMax :: a }
  deriving (Bounded, Eq, Ord, Show)

instance forall a . Ord a => Semigroup (Max a) where
  Max a <> Max b = Max (a `max` b)
  stimes = stimesIdempotent

instance forall a . (Ord a, Bounded a) => Monoid (Max a) where
  mempty = Max minBound

---------------------

newtype Min a = Min { getMin :: a }
  deriving (Bounded, Eq, Ord, Show)

instance forall a . Ord a => Semigroup (Min a) where
  Min a <> Min b = Min (a `min` b)
  stimes = stimesIdempotent

instance forall a . (Ord a, Bounded a) => Monoid (Min a) where
  mempty = Min maxBound

---------------------

newtype Sum a = Sum { getSum :: a }
  deriving (Bounded, Eq, Ord, Show)

instance forall a . Num a => Semigroup (Sum a) where
  Sum a <> Sum b = Sum (a + b)

instance forall a . (Num a) => Monoid (Sum a) where
  mempty = Sum 0

---------------------

newtype Product a = Product { getProduct :: a }
  deriving (Bounded, Eq, Ord, Show)

instance forall a . Num a => Semigroup (Product a) where
  Product a <> Product b = Product (a * b)

instance forall a . (Num a) => Monoid (Product a) where
  mempty = Product 1

---------------------

newtype All = All { getAll :: Bool }
  deriving (Bounded, Eq, Ord, Show)

instance Semigroup All where
  All a <> All b = All (a && b)

instance Monoid All where
  mempty = All True

---------------------

newtype Any = Any { getAny :: Bool }
  deriving (Bounded, Eq, Ord, Show)

instance Semigroup Any where
  Any a <> Any b = Any (a || b)

instance Monoid Any where
  mempty = Any False

---------------------

instance Semigroup Ordering where
  LT <> _ = LT
  EQ <> o = o
  GT <> _ = GT

instance Monoid Ordering where
  mempty = EQ

----------------------

data Arg a b = Arg a b
  deriving(Show)

type ArgMin a b = Min (Arg a b)

type ArgMax a b = Max (Arg a b)

instance Functor (Arg a) where
  fmap f (Arg x a) = Arg x (f a)

instance Eq a => Eq (Arg a b) where
  Arg a _ == Arg b _ = a == b

instance Ord a => Ord (Arg a b) where
  Arg a _ `compare` Arg b _ = compare a b
  min x@(Arg a _) y@(Arg b _)
    | a <= b    = x
    | otherwise = y
  max x@(Arg a _) y@(Arg b _)
    | a >= b    = x
    | otherwise = y

----------------------

newtype Alt f a = Alt (f a)
--  deriving (Show)
getAlt :: Alt f a -> f a
getAlt (Alt x) = x
{-
  deriving ( Generic     -- ^ @since base-4.8.0.0
           , Generic1    -- ^ @since base-4.8.0.0
           , Read        -- ^ @since base-4.8.0.0
           , Show        -- ^ @since base-4.8.0.0
           , Eq          -- ^ @since base-4.8.0.0
           , Ord         -- ^ @since base-4.8.0.0
           , Num         -- ^ @since base-4.8.0.0
           , Enum        -- ^ @since base-4.8.0.0
           , Monad       -- ^ @since base-4.8.0.0
           , MonadPlus   -- ^ @since base-4.8.0.0
           , Applicative -- ^ @since base-4.8.0.0
           , Alternative -- ^ @since base-4.8.0.0
           , Functor     -- ^ @since base-4.8.0.0
           )
-}

instance Alternative f => Semigroup (Alt f a) where
    Alt x <> Alt y = Alt (x <|> y)
    stimes = stimesMonoid

instance Alternative f => Monoid (Alt f a) where
    mempty = Alt empty

----------------------

-- This really belongs in Data.Semigroup,
-- but some functions have Monoid as in the context.

infixr 6 <>
class Semigroup a where
  (<>)    :: a -> a -> a
  sconcat :: NonEmpty a -> a
  stimes  :: (Integral b, Ord b) => b -> a -> a

  sconcat (a :| as) = go a as
    where go b (c:cs) = b <> go c cs
          go b []     = b

  stimes y0 x0
    | y0 <= 0   = error "stimes: positive multiplier expected"
    | otherwise = f x0 y0
    where
      f x y
        | even y = f (x <> x) (y `quot` 2)
        | y == 1 = x
        | otherwise = g (x <> x) (y `quot` 2) x
      g x y z
        | even y = g (x <> x) (y `quot` 2) z
        | y == 1 = x <> z
        | otherwise = g (x <> x) (y `quot` 2) (x <> z)

stimesIdempotent :: (Integral b, Ord b) => b -> a -> a
stimesIdempotent n x =
  if n <= 0 then error "stimesIdempotent: positive multiplier expected"
  else x

stimesIdempotentMonoid :: (Ord b, Integral b, Monoid a) => b -> a -> a
stimesIdempotentMonoid n x = case compare n 0 of
  LT -> error "stimesIdempotentMonoid: negative multiplier"
  EQ -> mempty
  GT -> x

stimesMonoid :: (Ord b, Integral b, Monoid a) => b -> a -> a
stimesMonoid n x0 = case compare n 0 of
  LT -> error "stimesMonoid: negative multiplier"
  EQ -> mempty
  GT -> f x0 n
    where
      f x y
        | even y = f (x `mappend` x) (y `quot` 2)
        | y == 1 = x
        | otherwise = g (x `mappend` x) (y `quot` 2) x
      g x y z
        | even y = g (x `mappend` x) (y `quot` 2) z
        | y == 1 = x `mappend` z
        | otherwise = g (x `mappend` x) (y `quot` 2) (x `mappend` z)

---------------------
