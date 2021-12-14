{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ConstraintKinds #-}
module Foundation.Monad.Exception
    ( MonadThrow(..)
    , MonadCatch(..)
    , MonadBracket(..)
    ) where

import           Basement.Compat.Base
import qualified Control.Exception as E

-- | Monad that can throw exception
class Monad m => MonadThrow m where
    -- | Throw immediatity an exception.
    -- Only a 'MonadCatch' monad will be able to catch the exception using 'catch'
    throw :: Exception e => e -> m a

-- | Monad that can catch exception
class MonadThrow m => MonadCatch m where
    catch :: Exception e => m a -> (e -> m a) -> m a

-- | Monad that can ensure cleanup actions are performed even in the
-- case of exceptions, both synchronous and asynchronous. This usually
-- excludes continuation-based monads.
class MonadCatch m => MonadBracket m where
    -- | A generalized version of the standard bracket function which
    -- allows distinguishing different exit cases.
    generalBracket
        :: m a
        -- ^ acquire some resource
        -> (a -> b -> m ignored1)
        -- ^ cleanup, no exception thrown
        -> (a -> E.SomeException -> m ignored2)
        -- ^ cleanup, some exception thrown. The exception will be rethrown
        -> (a -> m b)
        -- ^ inner action to perform with the resource
        -> m b

instance MonadThrow IO where
    throw = E.throwIO
instance MonadCatch IO where
    catch = E.catch
instance MonadBracket IO where
    generalBracket acquire onSuccess onException inner = E.mask $ \restore -> do
        x <- acquire
        res1 <- E.try $ restore $ inner x
        case res1 of
            Left (e1 :: E.SomeException) -> do
                -- explicitly ignore exceptions from the cleanup
                -- action so we keep the original exception
                E.uninterruptibleMask_ $ fmap (const ()) (onException x e1) `E.catch`
                    (\(_ :: E.SomeException) -> return ())
                E.throwIO e1
            Right y -> do
                -- Allow exceptions from the onSuccess function to propagate
                _ <- onSuccess x y
                return y
