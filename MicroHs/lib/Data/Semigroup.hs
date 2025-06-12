module Data.Semigroup(
  Semigroup(..),
  Endo(..),
  Dual(..),
  Max(..),
  Min(..),
  Sum(..),
  Product(..),
  All(..),
  Any(..),
  Arg(..), ArgMin, ArgMax,
  Alt(..),
  First(..),
  Last(..),
  stimesIdempotent, stimesIdempotentMonoid, stimesMonoid,
  diff, cycle1,
  ) where
import Data.Bool
import Data.Bounded
import Data.Coerce
import Data.Eq
import Data.Function
import Data.List.NonEmpty_Type
import Data.Monoid.Internal
import Data.Ord
import Data.Records
import Prelude qualified ()
import Text.Show

{-
newtype First a = First { getFirst :: a }
  deriving ( Bounded  -- ^ @since 4.9.0.0
           , Eq       -- ^ @since 4.9.0.0
           , Ord      -- ^ @since 4.9.0.0
           , Show     -- ^ @since 4.9.0.0
           , Read     -- ^ @since 4.9.0.0
           , Data     -- ^ @since 4.9.0.0
           , Generic  -- ^ @since 4.9.0.0
           , Generic1 -- ^ @since 4.9.0.0
           )

instance Enum a => Enum (First a) where
  succ (First a) = First (succ a)
  pred (First a) = First (pred a)
  toEnum = First . toEnum
  fromEnum = fromEnum . getFirst
  enumFrom (First a) = First `fmap` enumFrom a
  enumFromThen (First a) (First b) = First `fmap` enumFromThen a b
  enumFromTo (First a) (First b) = First `fmap` enumFromTo a b
  enumFromThenTo (First a) (First b) (First c) = First `fmap` enumFromThenTo a b c
-}

newtype First a = First { getFirst :: a }
  deriving(Eq, Ord, Show, Bounded)

instance Semigroup (First a) where
  a <> _ = a
  stimes = stimesIdempotent
  sconcat (x :| _) = x

{-
-- | @since 4.9.0.0
instance Functor First where
  fmap f (First x) = First (f x)

-- | @since 4.9.0.0
instance Foldable First where
  foldMap f (First a) = f a

-- | @since 4.9.0.0
instance Traversable First where
  traverse f (First a) = First `fmap` f a

-- | @since 4.9.0.0
instance Applicative First where
  pure x = First x
  a <* _ = a
  _ *> a = a
  (<*>) = coerce
  liftA2 = coerce

-- | @since 4.9.0.0
instance Monad First where
  (>>) = (*>)
  First a >>= f = f a

-- | @since 4.9.0.0
instance MonadFix First where
  mfix f = fix (f . getFirst)
-}

{-
newtype Last a = Last { getLast :: a }
  deriving ( Bounded  -- ^ @since 4.9.0.0
           , Eq       -- ^ @since 4.9.0.0
           , Ord      -- ^ @since 4.9.0.0
           , Show     -- ^ @since 4.9.0.0
           , Read     -- ^ @since 4.9.0.0
           , Data     -- ^ @since 4.9.0.0
           , Generic  -- ^ @since 4.9.0.0
           , Generic1 -- ^ @since 4.9.0.0
           )

-- | @since 4.9.0.0
instance Enum a => Enum (Last a) where
  succ (Last a) = Last (succ a)
  pred (Last a) = Last (pred a)
  toEnum = Last . toEnum
  fromEnum = fromEnum . getLast
  enumFrom (Last a) = Last `fmap` enumFrom a
  enumFromThen (Last a) (Last b) = Last `fmap` enumFromThen a b
  enumFromTo (Last a) (Last b) = Last `fmap` enumFromTo a b
  enumFromThenTo (Last a) (Last b) (Last c) = Last `fmap` enumFromThenTo a b c
-}

newtype Last a = Last { getLast :: a }
  deriving(Eq, Ord, Show, Bounded)

instance Semigroup (Last a) where
  _ <> b = b
  stimes = stimesIdempotent

{-
-- | @since 4.9.0.0
instance Functor Last where
  fmap f (Last x) = Last (f x)
  a <$ _ = Last a

-- | @since 4.9.0.0
instance Foldable Last where
  foldMap f (Last a) = f a

-- | @since 4.9.0.0
instance Traversable Last where
  traverse f (Last a) = Last `fmap` f a

-- | @since 4.9.0.0
instance Applicative Last where
  pure = Last
  a <* _ = a
  _ *> a = a
  (<*>) = coerce
  liftA2 = coerce

-- | @since 4.9.0.0
instance Monad Last where
  (>>) = (*>)
  Last a >>= f = f a

-- | @since 4.9.0.0
instance MonadFix Last where
  mfix f = fix (f . getLast)
-}

diff :: Semigroup m => m -> Endo m
diff = Endo . (<>)

cycle1 :: Semigroup m => m -> m
cycle1 xs = xs' where xs' = xs <> xs'
