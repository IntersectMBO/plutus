-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Traversable
-- Copyright   :  Conor McBride and Ross Paterson 2005
-- License     :  BSD-style (see the LICENSE file in the distribution)
--
-- Maintainer  :  libraries@haskell.org
-- Stability   :  stable
-- Portability :  portable
--
-- Class of data structures that can be traversed from left to right,
-- performing an action on each element.  Instances are expected to satisfy
-- the listed [laws](#laws).
-----------------------------------------------------------------------------

module Data.Traversable (
    -- * The 'Traversable' class
    Traversable(..),
    -- * Utility functions
    for,
    forM,
    forAccumM,
    mapAccumL,
    mapAccumR,
    mapAccumM,
    -- * General definitions for superclass methods
    fmapDefault,
    foldMapDefault,
    ) where
import Control.Applicative
import Control.Error
import Control.Monad (Monad (..), MonadPlus (..), liftM)
import Prelude qualified ()
import Primitives
--import Data.Coerce
import Data.Either
import Data.Foldable
import Data.Foldable.Internal (StateL (..), StateR (..), StateT (..), runStateL, runStateR,
                               runStateT)
import Data.Function
import Data.Functor
import Data.Functor.Const
import Data.Functor.Identity
import Data.List qualified as List
import Data.List_Type
import Data.Maybe
import Data.Monoid.Internal
import Data.Proxy
--import Data.Ord ( Down(..) )
--import Data.Proxy ( Proxy(..) )

class (Functor t, Foldable t) => Traversable (t :: Type -> Type) where

    traverse :: forall (f :: Type -> Type) a b . Applicative f => (a -> f b) -> t a -> f (t b)
    traverse f = sequenceA . fmap f

    sequenceA :: forall (f :: Type -> Type) a . Applicative f => t (f a) -> f (t a)
    sequenceA = traverse id

    mapM :: forall (m :: Type -> Type) a b . Monad m => (a -> m b) -> t a -> m (t b)
    mapM = traverse

    sequence :: forall (m :: Type -> Type) a . Monad m => t (m a) -> m (t a)
    sequence = sequenceA

instance Traversable Maybe where
  traverse _ Nothing  = pure Nothing
  traverse f (Just x) = Just <$> f x

instance Traversable [] where
  traverse f = List.foldr cons_f (pure [])
    where cons_f x ys = liftA2 (:) (f x) ys

instance Traversable (Either a) where
  traverse _ (Left x)  = pure (Left x)
  traverse f (Right y) = Right <$> f y

instance Traversable Identity where
  traverse f (Identity a) = Identity <$> f a

instance Traversable Proxy where
  traverse _ _ = pure Proxy

instance Traversable (Const m) where
  traverse _ (Const m) = pure $ Const m

{-
-- | @since 4.15
deriving instance Traversable Solo

-- | @since 4.7.0.0
instance Traversable ((,) a) where
    traverse f (x, y) = (,) x <$> f y

-- | @since 2.01
instance Ix i => Traversable (Array i) where
    traverse f arr = listArray (bounds arr) `fmap` traverse f (elems arr)

-- | @since 4.7.0.0
instance Traversable Proxy where
    traverse _ _ = pure Proxy
    {-# INLINE traverse #-}
    sequenceA _ = pure Proxy
    {-# INLINE sequenceA #-}
    mapM _ _ = pure Proxy
    {-# INLINE mapM #-}
    sequence _ = pure Proxy
    {-# INLINE sequence #-}

-- | @since 4.7.0.0
instance Traversable (Const m) where
    traverse _ (Const m) = pure $ Const m

-- | @since 4.8.0.0
instance Traversable Dual where
    traverse f (Dual x) = Dual <$> f x

-- | @since 4.8.0.0
instance Traversable Sum where
    traverse f (Sum x) = Sum <$> f x

-- | @since 4.8.0.0
instance Traversable Product where
    traverse f (Product x) = Product <$> f x

-- | @since 4.8.0.0
instance Traversable First where
    traverse f (First x) = First <$> traverse f x

-- | @since 4.8.0.0
instance Traversable Last where
    traverse f (Last x) = Last <$> traverse f x

-- | @since 4.12.0.0
instance (Traversable f) => Traversable (Alt f) where
    traverse f (Alt x) = Alt <$> traverse f x

-- | @since 4.12.0.0
instance (Traversable f) => Traversable (Ap f) where
    traverse f (Ap x) = Ap <$> traverse f x

-- | @since 4.9.0.0
instance Traversable ZipList where
    traverse f (ZipList x) = ZipList <$> traverse f x

instance Traversable (Arg a) where
  traverse f (Arg x a) = Arg x `fmap` f a

-- Instances for GHC.Generics
-- | @since 4.9.0.0
instance Traversable U1 where
    traverse _ _ = pure U1
    {-# INLINE traverse #-}
    sequenceA _ = pure U1
    {-# INLINE sequenceA #-}
    mapM _ _ = pure U1
    {-# INLINE mapM #-}
    sequence _ = pure U1
    {-# INLINE sequence #-}

-- | @since 4.9.0.0
deriving instance Traversable V1

-- | @since 4.9.0.0
deriving instance Traversable Par1

-- | @since 4.9.0.0
deriving instance Traversable f => Traversable (Rec1 f)

-- | @since 4.9.0.0
deriving instance Traversable (K1 i c)

-- | @since 4.9.0.0
deriving instance Traversable f => Traversable (M1 i c f)

-- | @since 4.9.0.0
deriving instance (Traversable f, Traversable g) => Traversable (f :+: g)

-- | @since 4.9.0.0
deriving instance (Traversable f, Traversable g) => Traversable (f :*: g)

-- | @since 4.9.0.0
deriving instance (Traversable f, Traversable g) => Traversable (f :.: g)

-- | @since 4.9.0.0
deriving instance Traversable UAddr

-- | @since 4.9.0.0
deriving instance Traversable UChar

-- | @since 4.9.0.0
deriving instance Traversable UDouble

-- | @since 4.9.0.0
deriving instance Traversable UFloat

-- | @since 4.9.0.0
deriving instance Traversable UInt

-- | @since 4.9.0.0
deriving instance Traversable UWord

-- Instance for Data.Ord
-- | @since 4.12.0.0
deriving instance Traversable Down
-}
-- general functions

-- | 'for' is 'traverse' with its arguments flipped. For a version
-- that ignores the results see 'Data.Foldable.for_'.
for :: forall (t :: Type -> Type) (f :: Type -> Type) a b . (Traversable t, Applicative f) => t a -> (a -> f b) -> f (t b)
for = flip traverse

forM :: forall (t :: Type -> Type) (m :: Type -> Type) a b . (Traversable t, Monad m) => t a -> (a -> m b) -> m (t b)
forM = flip mapM

mapAccumL :: forall t s a b. Traversable t
          => (s -> a -> (s, b)) -> s -> t a -> (s, t b)
mapAccumL f s t =
  runStateL (traverse (StateL . flip f) t) s
  --coerce (traverse @t @(StateL s) @a @b) (flip f) t s

mapAccumR :: forall t s a b. Traversable t
          => (s -> a -> (s, b)) -> s -> t a -> (s, t b)
mapAccumR f s t =
  runStateR (traverse (StateR . flip f) t) s
  --coerce (traverse @t @(StateR s) @a @b) (flip f) t s

mapAccumM
  :: forall m t s a b. (Monad m, Traversable t)
  => (s -> a -> m (s, b))
  -> s -> t a -> m (s, t b)
mapAccumM f s t =
  runStateT (traverse (StateT . flip f) t) s
  -- coerce (mapM @t @(StateT s m) @a @b) (StateT #. flip f) t s

forAccumM
  :: (Monad m, Traversable t)
  => s -> t a -> (s -> a -> m (s, b)) -> m (s, t b)
forAccumM s t f = mapAccumM f s t

fmapDefault :: forall t a b . Traversable t
            => (a -> b) -> t a -> t b
fmapDefault f = runIdentity . traverse (Identity . f)

foldMapDefault :: forall t m a . (Traversable t, Monoid m)
               => (a -> m) -> t a -> m
foldMapDefault f = getConst . traverse (Const . f)

-----------------------

