module Control.Monad.Except.Extras where

import           Control.Monad.Error.Class (MonadError, catchError, throwError)
import           Control.Monad.Except      (ExceptT, runExceptT)

mapError :: (MonadError f m) => (e -> f) -> ExceptT e m a -> m a
mapError f action = do
    result <- runExceptT action
    case result of
      Left e  -> throwError (f e)
      Right v -> pure v
