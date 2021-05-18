{-# OPTIONS_GHC -fno-specialise #-}
{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}
module PlutusTx.Foldable (
  Foldable(..),
  -- * Special biased folds
  foldrM,
  foldlM,
  -- * Folding actions
  -- ** Applicative actions
  traverse_,
  for_,
  sequenceA_,
  sequence_,
  asum,
  -- ** Monadic actions
  mapM_,
  -- * Specialized folds
  concat,
  concatMap,
  and,
  or,
  any,
  all,
  -- * Searches
  notElem,
  find,
  -- * Other
  fold,
  foldr,
  foldl,
  toList,
  null,
  length,
  elem,
  sum,
  product
  ) where

import           Control.Applicative   (Alternative (..), Const (..))
import           Data.Coerce           (Coercible, coerce)
import           Data.Functor.Identity (Identity (..))
import           Data.Monoid           (First (..))
import           Data.Semigroup        (Dual (..), Endo (..), Product (..), Sum (..))
import           GHC.Exts              (build)
import           PlutusTx.Applicative  (Applicative (pure), (*>))
import           PlutusTx.Bool         (not)
import           PlutusTx.Eq           (Eq (..))
import           PlutusTx.Functor      (id)
import           PlutusTx.Monoid       (Monoid (..))
import           PlutusTx.Numeric      (AdditiveMonoid, AdditiveSemigroup ((+)), MultiplicativeMonoid)
import           PlutusTx.Semigroup    ((<>))
import           Prelude               (Bool (..), Either (..), Integer, Maybe (..), Monad (..), flip, (.))

-- | Plutus Tx version of 'Data.Foldable.Foldable'.
class Foldable t where
    -- | Plutus Tx version of 'Data.Foldable.foldMap'.
    foldMap :: Monoid m => (a -> m) -> t a -> m

    -- All the other methods are deliberately omitted,
    -- to make this a one-method class which has a simpler representation

instance Foldable [] where
    {-# INLINABLE foldMap #-}
    foldMap _ []     = mempty
    foldMap f (x:xs) = f x <> foldMap f xs

instance Foldable Maybe where
    {-# INLINABLE foldMap #-}
    foldMap _ Nothing  = mempty
    foldMap f (Just a) = f a

instance Foldable (Either c) where
    {-# INLINABLE foldMap #-}
    foldMap _ (Left _)  = mempty
    foldMap f (Right a) = f a

instance Foldable ((,) c) where
    {-# INLINABLE foldMap #-}
    foldMap f (_, a) = f a

instance Foldable Identity where
    {-# INLINABLE foldMap #-}
    foldMap f (Identity a) = f a

instance Foldable (Const c) where
    {-# INLINABLE foldMap #-}
    foldMap _ _ = mempty

-- | Plutus Tx version of 'Data.Foldable.fold'.
{-# INLINABLE fold #-}
fold :: (Foldable t, Monoid m) => t m -> m
fold = foldMap id

-- | Plutus Tx version of 'Data.Foldable.foldr'.
{-# INLINABLE foldr #-}
foldr :: Foldable t => (a -> b -> b) -> b -> t a -> b
foldr f z t = appEndo (foldMap (Endo #. f) t) z

-- | Plutus Tx version of 'Data.Foldable.foldl'.
{-# INLINABLE foldl #-}
foldl :: Foldable t => (b -> a -> b) -> b -> t a -> b
foldl f z t = appEndo (getDual (foldMap (Dual . Endo . flip f) t)) z

-- | Plutus Tx version of 'Data.Foldable.toList'.
toList :: Foldable t => t a -> [a]
{-# INLINE toList #-}
toList t = build (\ c n -> foldr c n t)

-- | Plutus Tx version of 'Data.Foldable.null'.
{-# INLINABLE null #-}
null :: Foldable t => t a -> Bool
null = foldr (\_ _ -> False) True

-- | Plutus Tx version of 'Data.Foldable.length'.
{-# INLINABLE length #-}
length :: Foldable t => t a -> Integer
length = foldl (\c _ -> c + 1) 0

-- | Plutus Tx version of 'Data.Foldable.elem'.
{-# INLINABLE elem #-}
elem :: (Foldable t, Eq a) => a -> t a -> Bool
elem = any . (==)

-- | Plutus Tx version of 'Data.Foldable.sum'.
{-# INLINEABLE sum #-}
sum :: (Foldable t, AdditiveMonoid a) => t a -> a
sum = getSum #. foldMap Sum

-- | Plutus Tx version of 'Data.Foldable.product'.
{-# INLINABLE product #-}
product :: (Foldable t, MultiplicativeMonoid a) => t a -> a
product = getProduct #. foldMap Product



-- | Plutus Tx version of 'Data.Foldable.foldrM'.
foldrM :: (Foldable t, Monad m) => (a -> b -> m b) -> b -> t a -> m b
foldrM f z0 xs = foldl c return xs z0
  where c k x z = f x z >>= k
        {-# INLINE c #-}

-- | Plutus Tx version of 'Data.Foldable.foldlM'.
foldlM :: (Foldable t, Monad m) => (b -> a -> m b) -> b -> t a -> m b
foldlM f z0 xs = foldr c return xs z0
  where c x k z = f z x >>= k
        {-# INLINE c #-}

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

-- | Plutus Tx version of 'Data.Foldable.sequence_'.
sequence_ :: (Foldable t, Monad m) => t (m a) -> m ()
sequence_ = foldr c (return ())
  where c m k = m >> k
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

-- | Plutus Tx version of 'Data.Foldable.and'.
{-# INLINABLE and #-}
and :: Foldable t => t Bool -> Bool
and = product

-- | Plutus Tx version of 'Data.Foldable.or'.
{-# INLINABLE or #-}
or :: Foldable t => t Bool -> Bool
or = sum

-- | Plutus Tx version of 'Data.Foldable.any'.
{-# INLINABLE any #-}
any :: Foldable t => (a -> Bool) -> t a -> Bool
any p = getSum #. foldMap (Sum #. p)

-- | Plutus Tx version of 'Data.Foldable.all'.
{-# INLINABLE all #-}
all :: Foldable t => (a -> Bool) -> t a -> Bool
all p = getProduct #. foldMap (Product #. p)

-- | Plutus Tx version of 'Data.Foldable.notElem'.
{-# INLINABLE notElem #-}
notElem :: (Foldable t, Eq a) => a -> t a -> Bool
notElem x = not . elem x

-- | Plutus Tx version of 'Data.Foldable.find'.
{-# INLINABLE find #-}
find :: Foldable t => (a -> Bool) -> t a -> Maybe a
find p = getFirst . foldMap (\ x -> First (if p x then Just x else Nothing))

(#.) :: Coercible b c => (b -> c) -> (a -> b) -> (a -> c)
(#.) _f = coerce
{-# INLINE (#.) #-}

{-# INLINABLE mapM_ #-}
mapM_ :: (Foldable t, Monad m) => (a -> m b) -> t a -> m ()
mapM_ f = foldr c (return ())
  -- See Note [List fusion and continuations in 'c']
  where c x k = f x >> k
        {-# INLINE c #-}
