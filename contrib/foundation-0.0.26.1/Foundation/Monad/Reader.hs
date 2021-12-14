-- |
-- The Reader monad transformer.
--
-- This is useful to keep a non-modifiable value
-- in a context
{-# LANGUAGE ConstraintKinds #-}
module Foundation.Monad.Reader
    ( -- * MonadReader
      MonadReader(..)
    , -- * ReaderT
      ReaderT
    , runReaderT
    ) where

import Basement.Compat.Base (($), (.), const)
import Foundation.Monad.Base
import Foundation.Monad.Exception

class Monad m => MonadReader m where
    type ReaderContext m
    ask :: m (ReaderContext m)

-- | Reader Transformer
newtype ReaderT r m a = ReaderT { runReaderT :: r -> m a }

instance Functor m => Functor (ReaderT r m) where
    fmap f m = ReaderT $ fmap f . runReaderT m
    {-# INLINE fmap #-}

instance Applicative m => Applicative (ReaderT r m) where
    pure a     = ReaderT $ const (pure a)
    {-# INLINE pure #-}
    fab <*> fa = ReaderT $ \r -> runReaderT fab r <*> runReaderT fa r
    {-# INLINE (<*>) #-}

instance Monad m => Monad (ReaderT r m) where
    return a = ReaderT $ const (return a)
    {-# INLINE return #-}
    ma >>= mab = ReaderT $ \r -> runReaderT ma r >>= \a -> runReaderT (mab a) r
    {-# INLINE (>>=) #-}

instance (Monad m, MonadFix m) => MonadFix (ReaderT s m) where
    mfix f = ReaderT $ \r -> mfix $ \a -> runReaderT (f a) r
    {-# INLINE mfix #-}

instance MonadTrans (ReaderT r) where
    lift f = ReaderT $ const f
    {-# INLINE lift #-}

instance MonadIO m => MonadIO (ReaderT r m) where
    liftIO f = lift (liftIO f)
    {-# INLINE liftIO #-}

instance MonadFailure m => MonadFailure (ReaderT r m) where
    type Failure (ReaderT r m) = Failure m
    mFail e = ReaderT $ \_ -> mFail e

instance MonadThrow m => MonadThrow (ReaderT r m) where
    throw e = ReaderT $ \_ -> throw e

instance MonadCatch m => MonadCatch (ReaderT r m) where
    catch (ReaderT m) c = ReaderT $ \r -> m r `catch` (\e -> runReaderT (c e) r)

instance MonadBracket m => MonadBracket (ReaderT r m) where
    generalBracket acq cleanup cleanupExcept innerAction = do
        c <- ask
        lift $ generalBracket (runReaderT acq c)
                              (\a b -> runReaderT (cleanup a b) c)
                              (\a exn -> runReaderT (cleanupExcept a exn) c)
                              (\a -> runReaderT (innerAction a) c)

instance Monad m => MonadReader (ReaderT r m) where
    type ReaderContext (ReaderT r m) = r
    ask = ReaderT return
