{-# LANGUAGE TupleSections #-}
{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}
module Language.PlutusTx.Traversable (Traversable(..), sequenceA, mapM, sequence, for, fmapDefault, foldMapDefault) where

import           Control.Applicative           (Const (..))
import           Data.Coerce                   (coerce)
import           Data.Functor.Identity         (Identity (..))
import           Language.PlutusTx.Applicative (Applicative (..), liftA2)
import           Language.PlutusTx.Foldable    (Foldable)
import           Language.PlutusTx.Functor     (Functor, id, (<$>))
import           Language.PlutusTx.Monoid      (Monoid)
import           Prelude                       (Either (..), Maybe (..), flip)

-- | Functors representing data structures that can be traversed from
-- left to right.
--
-- A definition of 'traverse' must satisfy the following laws:
--
-- [Naturality]
--   @t . 'traverse' f = 'traverse' (t . f)@
--   for every applicative transformation @t@
--
-- [Identity]
--   @'traverse' 'Identity' = 'Identity'@
--
-- [Composition]
--   @'traverse' ('Data.Functor.Compose.Compose' . 'fmap' g . f)
--     = 'Data.Functor.Compose.Compose' . 'fmap' ('traverse' g) . 'traverse' f@
--
-- where an /applicative transformation/ is a function
--
-- @t :: (Applicative f, Applicative g) => f a -> g a@
--
-- preserving the 'Applicative' operations, i.e.
--
-- @
-- t ('pure' x) = 'pure' x
-- t (f '<*>' x) = t f '<*>' t x
-- @
--
-- and the identity functor 'Identity' and composition functors
-- 'Data.Functor.Compose.Compose' are from "Data.Functor.Identity" and
-- "Data.Functor.Compose".
--
-- A result of the naturality law is a purity law for 'traverse'
--
-- @'traverse' 'pure' = 'pure'@
--
-- (The naturality law is implied by parametricity and thus so is the
-- purity law [1, p15].)
--
-- Instances are similar to 'Functor', e.g. given a data type
--
-- > data Tree a = Empty | Leaf a | Node (Tree a) a (Tree a)
--
-- a suitable instance would be
--
-- > instance Traversable Tree where
-- >    traverse f Empty = pure Empty
-- >    traverse f (Leaf x) = Leaf <$> f x
-- >    traverse f (Node l k r) = Node <$> traverse f l <*> f k <*> traverse f r
--
-- This is suitable even for abstract types, as the laws for '<*>'
-- imply a form of associativity.
--
-- The superclass instances should satisfy the following:
--
--  * In the 'Functor' instance, 'fmap' should be equivalent to traversal
--    with the identity applicative functor ('fmapDefault').
--
--  * In the 'Foldable' instance, 'Language.PlutusTx.foldMap' should be
--    equivalent to traversal with a constant applicative functor
--    ('foldMapDefault').
--
-- References:
-- [1] The Essence of the Iterator Pattern, Jeremy Gibbons and Bruno C. d. S. Oliveira
class (Functor t, Foldable t) => Traversable t where
    -- | Map each element of a structure to an action, evaluate these actions
    -- from left to right, and collect the results. For a version that ignores
    -- the results see 'Language.PlutusTx.traverse_'.
    traverse :: Applicative f => (a -> f b) -> t a -> f (t b)

    -- All the other methods are deliberately omitted,
    -- to make this a one-method class which has a simpler representation


instance Traversable [] where
    {-# INLINABLE traverse #-}
    traverse f = go
      where
        go []     = pure []
        go (x:xs) = liftA2 (:) (f x) (go xs)

instance Traversable Maybe where
    {-# INLINABLE traverse #-}
    traverse _ Nothing  = pure Nothing
    traverse f (Just a) = Just <$> f a

instance Traversable (Either c) where
    {-# INLINABLE traverse #-}
    traverse _ (Left a)  = pure (Left a)
    traverse f (Right a) = Right <$> f a

instance Traversable ((,) c) where
    {-# INLINABLE traverse #-}
    traverse f (c, a) = (c,) <$> f a

instance Traversable Identity where
    {-# INLINABLE traverse #-}
    traverse f (Identity a) = Identity <$> f a

instance Traversable (Const c) where
    {-# INLINABLE traverse #-}
    traverse _ (Const c) = pure (Const c)

-- | Evaluate each action in the structure from left to right, and
-- collect the results. For a version that ignores the results
-- see 'Language.PlutusTx.sequenceA_'.
sequenceA :: (Traversable t, Applicative f) => t (f a) -> f (t a)
{-# INLINE sequenceA #-}
sequenceA = traverse id

-- | Same as 'sequenceA', for backwards compatibility.
sequence :: (Traversable t, Applicative f) => t (f a) -> f (t a)
{-# INLINE sequence #-}
sequence = sequenceA

-- | Same as 'traverse', for backwards compatibility.
mapM :: (Traversable t, Applicative f) => (a -> f b) -> t a -> f (t b)
{-# INLINE mapM #-}
mapM = traverse

-- | 'for' is 'traverse' with its arguments flipped. For a version
-- that ignores the results see 'Language.PlutusTx.for_'.
for :: (Traversable t, Applicative f) => t a -> (a -> f b) -> f (t b)
{-# INLINE for #-}
for = flip traverse

-- | This function may be used as a value for `fmap` in a `Functor`
--   instance, provided that 'traverse' is defined. (Using
--   `fmapDefault` with a `Traversable` instance defined only by
--   'sequenceA' will result in infinite recursion.)
--
-- @
-- 'fmapDefault' f ≡ 'runIdentity' . 'traverse' ('Identity' . f)
-- @
fmapDefault :: forall t a b . Traversable t
            => (a -> b) -> t a -> t b
{-# INLINE fmapDefault #-}
fmapDefault = coerce (traverse :: (a -> Identity b) -> t a -> Identity (t b))

-- | This function may be used as a value for `Language.PlutusTx.foldMap`
-- in a `Foldable` instance.
--
-- @
-- 'foldMapDefault' f ≡ 'getConst' . 'traverse' ('Const' . f)
-- @
foldMapDefault :: forall t m a . (Traversable t, Monoid m)
               => (a -> m) -> t a -> m
{-# INLINE foldMapDefault #-}
foldMapDefault = coerce (traverse :: (a -> Const m ()) -> t a -> Const m (t ()))
