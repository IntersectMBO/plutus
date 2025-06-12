{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE Trustworthy         #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Bitraversable
-- Copyright   :  (C) 2011-2016 Edward Kmett
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  libraries@haskell.org
-- Stability   :  provisional
-- Portability :  portable
--
-- @since 4.10.0.0
----------------------------------------------------------------------------
module Data.Bitraversable
  ( Bitraversable(..)
  , bisequenceA
  , bisequence
  , bimapM
  , bifor
  , biforM
  , bimapAccumL
  , bimapAccumR
--  , bimapDefault
--  , bifoldMapDefault
  ) where

import Control.Applicative
import Data.Bifoldable
import Data.Bifunctor
-- Data.Coerce
import Data.Foldable.Internal (StateL (..), StateR (..), runStateL, runStateR)
import Data.Functor.Identity (Identity (..))

class (Bifunctor t, Bifoldable t) => Bitraversable t where
  bitraverse :: Applicative f => (a -> f c) -> (b -> f d) -> t a b -> f (t c d)

bisequenceA :: (Bitraversable t, Applicative f) => t (f a) (f b) -> f (t a b)
bisequenceA = bisequence

bimapM :: (Bitraversable t, Applicative f)
       => (a -> f c) -> (b -> f d) -> t a b -> f (t c d)
bimapM = bitraverse

bisequence :: (Bitraversable t, Applicative f) => t (f a) (f b) -> f (t a b)
bisequence = bitraverse id id

{-
instance Bitraversable (,) where
  bitraverse f g ~(a, b) = liftA2 (,) (f a) (g b)

instance Bitraversable ((,,) x) where
  bitraverse f g ~(x, a, b) = liftA2 ((,,) x) (f a) (g b)

instance Bitraversable ((,,,) x y) where
  bitraverse f g ~(x, y, a, b) = liftA2 ((,,,) x y) (f a) (g b)

instance Bitraversable ((,,,,) x y z) where
  bitraverse f g ~(x, y, z, a, b) = liftA2 ((,,,,) x y z) (f a) (g b)

instance Bitraversable ((,,,,,) x y z w) where
  bitraverse f g ~(x, y, z, w, a, b) = liftA2 ((,,,,,) x y z w) (f a) (g b)

instance Bitraversable ((,,,,,,) x y z w v) where
  bitraverse f g ~(x, y, z, w, v, a, b) =
    liftA2 ((,,,,,,) x y z w v) (f a) (g b)
-}

instance Bitraversable Either where
  bitraverse f _ (Left a)  = Left <$> f a
  bitraverse _ g (Right b) = Right <$> g b

instance Bitraversable Const where
  bitraverse f _ (Const a) = Const <$> f a

bifor :: (Bitraversable t, Applicative f)
      => t a b -> (a -> f c) -> (b -> f d) -> f (t c d)
bifor t f g = bitraverse f g t

biforM :: (Bitraversable t, Applicative f)
       => t a b -> (a -> f c) -> (b -> f d) -> f (t c d)
biforM = bifor

bimapAccumL :: Bitraversable t => (a -> b -> (a, c)) -> (a -> d -> (a, e))
            -> a -> t b d -> (a, t c e)
bimapAccumL f g s t
  = runStateL (bitraverse (StateL . flip f) (StateL . flip g) t) s

bimapAccumR :: Bitraversable t => (a -> b -> (a, c)) -> (a -> d -> (a, e))
            -> a -> t b d -> (a, t c e)
bimapAccumR f g s t
  = runStateR (bitraverse (StateR . flip f) (StateR . flip g) t) s

{-
bimapDefault = coerce
  (bitraverse :: (a -> Identity b)
              -> (c -> Identity d) -> t a c -> Identity (t b d))

bifoldMapDefault :: forall t m a b . (Bitraversable t, Monoid m)
                 => (a -> m) -> (b -> m) -> t a b -> m
bifoldMapDefault = coerce
  (bitraverse :: (a -> Const m ())
              -> (b -> Const m ()) -> t a b -> Const m (t () ()))
-}
