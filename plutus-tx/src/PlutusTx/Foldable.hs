{-# LANGUAGE LambdaCase #-}
{-# OPTIONS_GHC -fno-specialise #-}
{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}
module PlutusTx.Foldable (
  Foldable(..),
  -- * Applicative actions
  traverse_,
  for_,
  sequenceA_,
  asum,
  -- * Specialized folds
  concat,
  concatMap,
  -- * Other
  foldMap,
  fold,
  foldl,
  toList,
  length,
  sum,
  product
  ) where

import Control.Applicative (Alternative (..), Const (..))
import Data.Functor.Identity (Identity (..))
import GHC.Exts (build)
import PlutusTx.Applicative (Applicative (pure), (*>))
import PlutusTx.Base
import PlutusTx.Builtins (Integer)
import PlutusTx.Either (Either (..))
import PlutusTx.Maybe (Maybe (..))
import PlutusTx.Monoid (Monoid (..))
import PlutusTx.Numeric
import PlutusTx.Semigroup ((<>))

-- | Plutus Tx version of 'Data.Foldable.Foldable'.
class Foldable t where
    -- | Plutus Tx version of 'Data.Foldable.foldr'.
    foldr :: (a -> b -> b) -> b -> t a -> b

    -- All the other methods are deliberately omitted,
    -- to make this a one-method class which has a simpler representation

instance Foldable [] where
    {-# INLINABLE foldr #-}
    foldr f z = go
      where
        go = \case
          []     -> z
          x : xs -> f x (go xs)

instance Foldable Maybe where
    {-# INLINABLE foldr #-}
    foldr f z = \case
      Nothing -> z
      Just a  -> f a z

instance Foldable (Either c) where
    {-# INLINABLE foldr #-}
    foldr f z = \case
      Left _  -> z
      Right a -> f a z

instance Foldable ((,) c) where
    {-# INLINABLE foldr #-}
    foldr f z (_, a) = f a z

instance Foldable Identity where
    {-# INLINABLE foldr #-}
    foldr f z (Identity a) = f a z

instance Foldable (Const c) where
    {-# INLINABLE foldr #-}
    foldr _ z _ = z

-- | Plutus Tx version of 'Data.Foldable.fold'.
{-# INLINABLE fold #-}
fold :: (Foldable t, Monoid m) => t m -> m
fold = foldMap id

-- | Plutus Tx version of 'Data.Foldable.foldMap'.
foldMap :: (Foldable t, Monoid m) => (a -> m) -> t a -> m
foldMap f = foldr ((<>) . f) mempty

-- | Plutus Tx version of 'Data.Foldable.foldl'.
{-# INLINABLE foldl #-}
foldl :: Foldable t => (b -> a -> b) -> b -> t a -> b
foldl f z t = foldr (\a g b -> g (f b a)) id t z

-- | Plutus Tx version of 'Data.Foldable.toList'.
toList :: Foldable t => t a -> [a]
{-# INLINE toList #-}
toList t = build (\ c n -> foldr c n t)

-- | Plutus Tx version of 'Data.Foldable.length'.
{-# INLINABLE length #-}
length :: Foldable t => t a -> Integer
length = foldr (\_ acc -> acc + 1) 0

-- | Plutus Tx version of 'Data.Foldable.sum'.
{-# INLINEABLE sum #-}
sum :: (Foldable t, AdditiveMonoid a) => t a -> a
sum = foldr (+) zero

-- | Plutus Tx version of 'Data.Foldable.product'.
{-# INLINABLE product #-}
product :: (Foldable t, MultiplicativeMonoid a) => t a -> a
product = foldr (*) one

-- | Plutus Tx version of 'Data.Foldable.traverse_'.
traverse_ :: (Foldable t, Applicative f) => (a -> f b) -> t a -> f ()
traverse_ f = foldr c (pure ())
  where c x k = f x *> k
        {-# INLINE c #-}

-- | Plutus Tx version of 'Data.Foldable.for_'.
for_ :: (Foldable t, Applicative f) => t a -> (a -> f b) -> f ()
{-# INLINE for_ #-}
for_ = flip traverse_

-- | Plutus Tx version of 'Data.Foldable.sequenceA_'.
sequenceA_ :: (Foldable t, Applicative f) => t (f a) -> f ()
sequenceA_ = foldr c (pure ())
  where c m k = m *> k
        {-# INLINE c #-}

-- | Plutus Tx version of 'Data.Foldable.asum'.
asum :: (Foldable t, Alternative f) => t (f a) -> f a
{-# INLINE asum #-}
asum = foldr (<|>) empty

-- | Plutus Tx version of 'Data.Foldable.concat'.
concat :: Foldable t => t [a] -> [a]
concat xs = build (\c n -> foldr (\x y -> foldr c y x) n xs)
{-# INLINE concat #-}

-- | Plutus Tx version of 'Data.Foldable.concatMap'.
concatMap :: Foldable t => (a -> [b]) -> t a -> [b]
concatMap f xs = build (\c n -> foldr (\x b -> foldr c b (f x)) n xs)
{-# INLINE concatMap #-}
