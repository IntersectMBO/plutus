module Control.Monad.Reader.Extra where

import Prelude
import Control.Monad.Reader (ReaderT, runReaderT)
import Control.Monad.Reader.Class (class MonadAsk, asks)

mapEnvReaderT :: forall m e f a. MonadAsk f m => (f -> e) -> ReaderT e m a -> m a
mapEnvReaderT f action = do
  s <- asks f
  runReaderT action s
