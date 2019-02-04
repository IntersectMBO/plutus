module Control.Monad.Trace where

import           Control.Monad.Trans               (lift)
import           Control.Monad.Trans.Maybe         (MaybeT (MaybeT), runMaybeT)
import           Control.Monad.Trans.Writer.Strict (Writer, runWriter)
import           Control.Monad.Writer.Class        (tell)
import           Data.Monoid                       (Last (Last))

------------------------------------------------------------
-- | `Trace` is a neat way to run a `Maybe` monad, but leave a trail behind
-- so that if it fails, we know what step it failed at.
type TraceMaybe a = MaybeT (Writer (Last a))

withTrace :: Monad m => Maybe a -> MaybeT m a
withTrace = MaybeT . pure

attempt :: a -> TraceMaybe a ()
attempt = lift . tell . pure

runTrace :: e -> TraceMaybe e a -> Either e a
runTrace def trace =
  case runWriter $ runMaybeT trace of
    (Just value, _)            -> Right value
    (Nothing, Last (Just msg)) -> Left msg
    (Nothing, Last Nothing)    -> Left def
