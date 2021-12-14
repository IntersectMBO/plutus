{-# LANGUAGE TupleSections #-}
module Foundation.Monad.State
    ( -- * MonadState
      MonadState(..)
    , get
    , put

    , -- * StateT
      StateT
    , runStateT
    ) where

import Basement.Compat.Bifunctor (first)
import Basement.Compat.Base (($), (.), const)
import Foundation.Monad.Base
import Control.Monad ((>=>))

class Monad m => MonadState m where
    type State m
    withState :: (State m -> (a, State m)) -> m a

get :: MonadState m => m (State m)
get = withState $ \s -> (s, s)

put :: MonadState m => State m -> m ()
put s = withState $ const ((), s)

-- | State Transformer
newtype StateT s m a = StateT { runStateT :: s -> m (a, s) }

instance Functor m => Functor (StateT s m) where
    fmap f m = StateT $ \s1 -> (first f) `fmap` runStateT m s1
    {-# INLINE fmap #-}

instance (Applicative m, Monad m) => Applicative (StateT s m) where
    pure a     = StateT $ \s -> (,s) `fmap` pure a
    {-# INLINE pure #-}
    fab <*> fa = StateT $ \s1 -> do
        (ab,s2) <- runStateT fab s1
        (a, s3) <- runStateT fa s2
        return (ab a, s3)
    {-# INLINE (<*>) #-}

instance (Functor m, Monad m) => Monad (StateT s m) where
    return a = StateT $ \s -> (,s) `fmap` return a
    {-# INLINE return #-}
    ma >>= mab = StateT $ runStateT ma >=> (\(a, s2) -> runStateT (mab a) s2)
    {-# INLINE (>>=) #-}

instance (Functor m, MonadFix m) => MonadFix (StateT s m) where
    mfix f = StateT $ \s -> mfix $ \ ~(a, _) -> runStateT (f a) s
    {-# INLINE mfix #-}

instance MonadTrans (StateT s) where
    lift f = StateT $ \s -> f >>= return . (,s)
    {-# INLINE lift #-}

instance (Functor m, MonadIO m) => MonadIO (StateT s m) where
    liftIO f = lift (liftIO f)
    {-# INLINE liftIO #-}

instance (Functor m, MonadFailure m) => MonadFailure (StateT s m) where
    type Failure (StateT s m) = Failure m
    mFail e = StateT $ \s -> ((,s) `fmap` mFail e)

instance (Functor m, MonadThrow m) => MonadThrow (StateT s m) where
    throw e = StateT $ \_ -> throw e

instance (Functor m, MonadCatch m) => MonadCatch (StateT s m) where
    catch (StateT m) c = StateT $ \s1 -> m s1 `catch` (\e -> runStateT (c e) s1)

instance (Functor m, Monad m) => MonadState (StateT s m) where
    type State (StateT s m) = s
    withState f = StateT $ return . f
