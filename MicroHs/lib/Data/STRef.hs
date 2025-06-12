module Data.STRef(
  STRef,
  newSTRef, readSTRef, writeSTRef, modifySTRef,
  ) where
import Control.Monad.ST_Type
import Data.IORef
import {-# SOURCE #-} Data.Typeable
import MiniPrelude
import Prelude qualified ()

newtype STRef s a = R (IORef a)
  deriving (Typeable)

newSTRef :: forall s a . a -> ST s (STRef s a)
newSTRef a = ST (R <$> newIORef a)

readSTRef :: forall s a . STRef s a -> ST s a
readSTRef (R p) = ST (readIORef p)

writeSTRef :: forall s a . STRef s a -> a -> ST s ()
writeSTRef (R p) a = ST (writeIORef p a)

modifySTRef :: forall s a . STRef s a -> (a -> a) -> ST s ()
modifySTRef (R p) f = ST (modifyIORef p f)
