module Data.MultiSet.Lens (multiSetOf) where

import Control.Lens

import Data.MultiSet

-- | Create a 'MultiSet' from a 'Getter', 'Fold', etc.
multiSetOf :: Getting (MultiSet a) s a -> s -> MultiSet a
-- same as 'setOf'
multiSetOf l = views l singleton
