module Data.Functor.Foldable.Monadic (cataM) where

import           Data.Functor.Foldable
import           PlutusPrelude

cataM :: (Recursive t, Traversable (Base t), Monad m) => (Base t a -> m a) -> t -> m a
cataM f = c where c = f <=< (traverse c . project)
