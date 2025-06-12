module Control.Monad.IO.Class (MonadIO(..)) where
import Control.Applicative
import Control.Monad
import Data.Char
import Prelude qualified ()
import System.IO

class (Monad m) => MonadIO m where
  liftIO :: IO a -> m a

instance MonadIO IO where
  liftIO io = io
