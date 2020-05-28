module Data.Foldable.Extra (interleave) where

import Control.Applicative (class Applicative, pure)
import Data.Foldable (class Foldable, intercalate)
import Data.Functor (map)
import Data.Monoid (class Monoid)

interleave :: forall m a. Applicative m => Foldable m => Monoid (m a) => a -> m a -> m a
interleave sep xs = intercalate (pure sep) (map pure xs)
