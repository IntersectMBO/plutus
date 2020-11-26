-- | Utils used internally.

module Text.PrettyBy.Internal.Utils
    ( view
    ) where

import           Control.Monad.Reader
import           Data.Functor.Const
import           Lens.Micro
import           Lens.Micro.Internal  ((#.))

-- | An inlined https://hackage.haskell.org/package/microlens-mtl-0.2.0.1/docs/Lens-Micro-Mtl.html#v:view
-- (just not to depend on this package).
view :: MonadReader s m => Getting a s a -> m a
view l = asks (getConst #. l Const)
{-# INLINE view #-}
