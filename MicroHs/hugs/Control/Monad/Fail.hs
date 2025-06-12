module Control.Monad.Fail(MonadFail(..)) where
import Prelude hiding (fail)

class Monad m => MonadFail m where
  fail :: String -> m a
  fail = error

instance MonadFail [] where
  fail _ = []
