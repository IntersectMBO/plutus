module Control.Monad.State.Extra where

import Control.Bind (bind, discard, pure)
import Control.Monad.State.Trans (class MonadState, StateT, runStateT)
import Data.Lens (Lens', assign, use)
import Data.Tuple (Tuple(..))

zoomStateT :: forall m s t a. MonadState s m => Lens' s t -> StateT t m a -> m a
zoomStateT l f = do
  s <- use l
  (Tuple a v) <- runStateT f s
  assign l v
  pure a
