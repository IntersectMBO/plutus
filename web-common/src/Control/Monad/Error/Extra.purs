module Control.Monad.Error.Extra where

import Control.Monad (pure, (=<<))
import Control.Monad.Except (Except)
import Control.Monad.Except.Trans (class MonadThrow, ExceptT, runExceptT, throwError)
import Data.Either (Either(..), either)
import Data.Function (($), (<<<))
import Data.Newtype (unwrap)

liftEither :: forall f e m a. MonadThrow f m => (e -> f) -> Either e a -> m a
liftEither f = either (throwError <<< f) pure

mapError :: forall m e f a. MonadThrow f m => (e -> f) -> Except e a -> m a
mapError f action = liftEither f $ unwrap $ runExceptT action

mapErrorT :: forall m e f a. MonadThrow f m => (e -> f) -> ExceptT e m a -> m a
mapErrorT f action = liftEither f =<< runExceptT action

toMonadThrow :: forall m e a. MonadThrow e m => Either e a -> m a
toMonadThrow (Left err) = throwError err

toMonadThrow (Right value) = pure value
