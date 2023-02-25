{-# OPTIONS_GHC -fno-specialise #-}
{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}
module PlutusTx.Foldable (
  Foldable(..),
  ToList (..),
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
  null,
  length,
  elem,
  sum,
  product
  ) where

import Control.Applicative (Alternative (..), Const (..))
import Data.Coerce (Coercible, coerce)
import Data.Functor.Identity (Identity (..))
import Data.Semigroup (Dual (..), Endo (..), Product (..), Sum (..))
import GHC.Exts (build)
import PlutusTx.Applicative (Applicative (pure), (*>))
import PlutusTx.Base
import PlutusTx.Bool (Bool (..), not, (&&), (||))
import PlutusTx.Builtins (Integer)
import PlutusTx.Either (Either (..))
import PlutusTx.Eq (Eq (..))
import PlutusTx.Maybe (Maybe (..))
import PlutusTx.Monoid (Monoid (..))
import PlutusTx.Numeric (AdditiveMonoid, AdditiveSemigroup ((+)), MultiplicativeMonoid)
import PlutusTx.Semigroup ((<>))

import Prelude qualified as Haskell (Monad, return, (>>), (>>=))

-- | Plutus Tx version of 'Data.Foldable.Foldable'.
--
-- Like many other Plutus Tx typeclasses, this class contains a single method, because
-- one method classes have much simpler representations in GHC Core than multiple method classes.
class Foldable t where
    -- | Plutus Tx version of 'Data.Foldable.foldMap'.
    foldMap :: Monoid m => (a -> m) -> t a -> m

-- | This class exists so that different types can provide custom `toList` definitions, which can
-- be much cheaper than the default definition.
--
-- It is kept separate from `Foldable`, because one-method classes have simpler representations
-- in GHC Core.
class Foldable t => ToList t where
    {-# INLINABLE toList #-}
    -- | Plutus Tx version of 'Data.Foldable.toList'.
    toList :: t a -> [a]
    toList t = build (\ c n -> foldr c n t)

instance Foldable [] where
    {-# INLINABLE foldMap #-}
    foldMap _ []     = mempty
    foldMap f (x:xs) = f x <> foldMap f xs

instance ToList [] where
    {-# INLINABLE toList #-}
    toList = id

instance Foldable Maybe where
    {-# INLINABLE foldMap #-}
    foldMap _ Nothing  = mempty
    foldMap f (Just a) = f a

instance ToList Maybe where
    {-# INLINABLE toList #-}
    toList Nothing  = []
    toList (Just a) = [a]

instance Foldable (Either c) where
    {-# INLINABLE foldMap #-}
    foldMap _ (Left _)  = mempty
    foldMap f (Right a) = f a

instance ToList (Either c) where
    {-# INLINABLE toList #-}
    toList (Left _)  = []
    toList (Right a) = [a]

instance Foldable ((,) c) where
    {-# INLINABLE foldMap #-}
    foldMap f (_, a) = f a

instance ToList ((,) c) where
    {-# INLINABLE toList #-}
    toList (_, a) = [a]

instance Foldable Identity where
    {-# INLINABLE foldMap #-}
    foldMap f (Identity a) = f a

instance ToList Identity where
    {-# INLINABLE toList #-}
    toList (Identity a) = [a]

instance Foldable (Const c) where
    {-# INLINABLE foldMap #-}
    foldMap _ _ = mempty

instance ToList (Const c) where
    {-# INLINABLE toList #-}
    toList _ = []

-- | Plutus Tx version of 'Data.Foldable.fold'.
{-# INLINABLE fold #-}
fold :: (Foldable t, Monoid m) => t m -> m
fold = foldMap id

-- | Plutus Tx version of 'Data.Foldable.foldr'.
{-# INLINABLE foldr #-}
foldr :: Foldable t => (a -> b -> b) -> b -> t a -> b
-- See Note [newtype field accessors in `base`]
foldr f z t = coerce (foldMap (Endo #. f) t) z

-- | Plutus Tx version of 'Data.Foldable.foldl'.
{-# INLINABLE foldl #-}
foldl :: Foldable t => (b -> a -> b) -> b -> t a -> b
-- See Note [newtype field accessors in `base`]
foldl f z t = coerce (foldMap (Dual . Endo . flip f) t) z

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
elem :: (ToList t, Eq a) => a -> t a -> Bool
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
foldrM :: (Foldable t, Haskell.Monad m) => (a -> b -> m b) -> b -> t a -> m b
foldrM f z0 xs = foldl c Haskell.return xs z0
  where c k x z = f x z Haskell.>>= k
        {-# INLINE c #-}

-- | Plutus Tx version of 'Data.Foldable.foldlM'.
foldlM :: (Foldable t, Haskell.Monad m) => (b -> a -> m b) -> b -> t a -> m b
foldlM f z0 xs = foldr c Haskell.return xs z0
  where c x k z = f z x Haskell.>>= k
        {-# INLINE c #-}

-- | Plutus Tx version of 'Data.Foldable.traverse_'.
traverse_ :: (Foldable t, Applicative f) => (a -> f b) -> t a -> f ()
traverse_ f = foldr c (pure ())
  where c x k = f x *> k
        {-# INLINE c #-}

-- | Plutus Tx version of 'Data.Foldable.sequence_'.
sequence_ :: (Foldable t, Haskell.Monad m) => t (m a) -> m ()
sequence_ = foldr c (Haskell.return ())
  where c m k = m Haskell.>> k
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

-- | Plutus Tx version of 'Data.Foldable.and'.
{-# INLINABLE and #-}
and :: ToList t => t Bool -> Bool
and = all id

-- | Plutus Tx version of 'Data.Foldable.or'.
{-# INLINABLE or #-}
or :: ToList t => t Bool -> Bool
or = any id

-- | Plutus Tx version of 'Data.Foldable.any'.
{-# INLINABLE any #-}
any :: ToList t => (a -> Bool) -> t a -> Bool
any p = go . toList
  where
    go []       = False
    go (x : xs) = p x || go xs

-- | Plutus Tx version of 'Data.Foldable.all'.
{-# INLINABLE all #-}
all :: ToList t => (a -> Bool) -> t a -> Bool
all p = go . toList
  where
    go []       = True
    go (x : xs) = p x && go xs

-- | Plutus Tx version of 'Data.Foldable.notElem'.
{-# INLINABLE notElem #-}
notElem :: (ToList t, Eq a) => a -> t a -> Bool
notElem x = not . elem x

-- | Plutus Tx version of 'Data.Foldable.find'.
{-# INLINABLE find #-}
find :: ToList t => (a -> Bool) -> t a -> Maybe a
-- See Note [newtype field accessors in `base`]
find p = go . toList
  where
    go []       = Nothing
    go (x : xs) = if p x then Just x else go xs

(#.) :: Coercible b c => (b -> c) -> (a -> b) -> (a -> c)
(#.) _f = coerce
{-# INLINE (#.) #-}

-- | Plutus Tx version of 'Data.Foldable.mapM_'.
{-# INLINABLE mapM_ #-}
mapM_ :: (Foldable t, Haskell.Monad m) => (a -> m b) -> t a -> m ()
mapM_ f = foldr c (Haskell.return ())
  where c x k = f x Haskell.>> k
        {-# INLINE c #-}
