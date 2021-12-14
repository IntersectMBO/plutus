-- |
-- Module      : Basement.Mappable
-- License     : BSD-style
-- Maintainer  : Nicolas Di Prima <nicolas@primetype.co.uk>
-- Stability   : experimental
-- Portability : portable
--
-- Class of collection that can be traversed from left to right,
-- performing an action on each element.
--
module Foundation.Collection.Mappable
    ( Mappable(..)
    , sequence_
    , traverse_
    , mapM_
    , forM
    , forM_
    ) where

import           Basement.Compat.Base
import qualified Data.Traversable
import           Basement.BoxedArray (Array)

-- | Functors representing data structures that can be traversed from
-- left to right.
--
-- Mostly like base's `Traversable` but applied to collections only.
--
class Functor collection => Mappable collection where
    {-# MINIMAL traverse | sequenceA #-}

    -- | Map each element of a structure to an action, evaluate these actions
    -- from left to right, and collect the results. For a version that ignores
    -- the results see 'Foundation.Collection.traverse_'.
    traverse :: Applicative f => (a -> f b)
                              -> collection a
                              -> f (collection b)
    traverse f = sequenceA . fmap f

    -- | Evaluate each actions of the given collections, from left to right,
    -- and collect the results. For a version that ignores the results, see
    -- `Foundation.Collection.sequenceA_`
    sequenceA :: Applicative f => collection (f a)
                               -> f (collection a)
    sequenceA = traverse id

    -- | Map each element of the collection to an action, evaluate these actions
    -- from left to right, and collect the results. For a version that ignores
    -- the results see 'Foundation.Collection.mapM_'.
    mapM :: (Applicative m, Monad m) => (a -> m b) -> collection a -> m (collection b)
    mapM = traverse

    -- | Evaluate each actions of the given collections, from left to right,
    -- and collect the results. For a version that ignores the results, see
    -- `Foundation.Collection.sequence_`
    sequence :: (Applicative m, Monad m) => collection (m a) -> m (collection a)
    sequence = sequenceA

-- | Map each element of a collection to an action, evaluate these
-- actions from left to right, and ignore the results. For a version
-- that doesn't ignore the results see 'Foundation.Collection.traverse`
traverse_ :: (Mappable col, Applicative f) => (a -> f b) -> col a -> f ()
traverse_ f col = traverse f col *> pure ()

-- | Evaluate each action in the collection from left to right, and
-- ignore the results. For a version that doesn't ignore the results
-- see 'Foundation.Collection.sequenceA'.
--sequenceA_ :: (Mappable col, Applicative f) => col (f a) -> f ()
--sequenceA_ col = sequenceA col *> pure ()

-- | Map each element of a collection to a monadic action, evaluate
-- these actions from left to right, and ignore the results. For a
-- version that doesn't ignore the results see
-- 'Foundation.Collection.mapM'.
mapM_ :: (Mappable col, Applicative m, Monad m) => (a -> m b) -> col a -> m ()
mapM_ f c = mapM f c *> return ()

-- | Evaluate each monadic action in the collection from left to right,
-- and ignore the results. For a version that doesn't ignore the
-- results see 'Foundation.Collection.sequence'.
sequence_ :: (Mappable col, Applicative m, Monad m) => col (m a) -> m ()
sequence_ c = sequence c *> return ()

-- | 'forM' is 'mapM' with its arguments flipped. For a version that
-- ignores the results see 'Foundation.Collection.forM_'.
forM :: (Mappable col, Applicative m, Monad m) => col a -> (a -> m b) -> m (col b)
forM = flip mapM

-- | 'forM_' is 'mapM_' with its arguments flipped. For a version that
-- doesn't ignore the results see 'Foundation.Collection.forM'.
forM_ :: (Mappable col, Applicative m, Monad m) => col a -> (a -> m b) -> m ()
forM_ = flip mapM_

----------------------------
-- Foldable instances
----------------------------

instance Mappable [] where
    {-# INLINE traverse #-}
    traverse = Data.Traversable.traverse

instance Mappable Array where
    -- | TODO: to optimise
    traverse f arr = fromList <$> traverse f (toList arr)
