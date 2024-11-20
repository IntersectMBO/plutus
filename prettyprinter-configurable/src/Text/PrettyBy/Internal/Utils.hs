-- | Utils used internally.
module Text.PrettyBy.Internal.Utils (
  view,
) where

import Control.Monad.Reader (MonadReader, asks)
import Data.Functor.Const (Const (Const, getConst))
import Lens.Micro (Getting)
import Lens.Micro.Internal ((#.))

-- | An inlined 'Lens.Micro.Mtl.view' (just not to depend on this package).
view :: (MonadReader s m) => Getting a s a -> m a
view l = asks (getConst #. l Const)
{-# INLINE view #-}
