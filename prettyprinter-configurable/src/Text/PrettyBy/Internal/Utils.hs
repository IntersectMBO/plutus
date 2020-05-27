module Text.PrettyBy.Internal.Utils
    ( view
    ) where

import           Control.Monad.Reader
import           Data.Functor.Const
import           Lens.Micro
import           Lens.Micro.Internal  (( #. ))

view :: MonadReader s m => Getting a s a -> m a
view l = asks (getConst #. l Const)
{-# INLINE view #-}
