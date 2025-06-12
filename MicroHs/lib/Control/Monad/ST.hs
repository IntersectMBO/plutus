module Control.Monad.ST(
  ST,
  runST,
  ) where
import Control.Monad.ST_Type
import MiniPrelude
import Prelude qualified ()
import Primitives (primPerformIO)

runST :: forall a . (forall s . ST s a) -> a
runST (ST ioa) = primPerformIO ioa

instance forall s . Functor (ST s) where
  fmap f (ST x) = ST (fmap f x)

instance forall s . Applicative (ST s) where
  pure x = ST (pure x)
  ST x <*> ST y = ST (x <*> y)

instance forall s . Monad (ST s) where
  ST x >>= f = ST (x >>= (unST . f))
