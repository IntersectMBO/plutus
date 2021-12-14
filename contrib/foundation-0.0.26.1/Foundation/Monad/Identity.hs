-- |
-- The identity monad transformer.
--
-- This is useful for functions parameterized by a monad transformer.
--
module Foundation.Monad.Identity
    ( IdentityT
    , runIdentityT
    ) where

import Basement.Compat.Base hiding (throw)
import Basement.Monad (MonadFailure(..))
import Foundation.Monad.MonadIO
import Foundation.Monad.Exception
import Foundation.Monad.Transformer

-- | Identity Transformer
newtype IdentityT m a = IdentityT { runIdentityT :: m a }

instance Functor m => Functor (IdentityT m) where
    fmap f (IdentityT m) = IdentityT (f `fmap` m)
    {-# INLINE fmap #-}

instance Applicative m => Applicative (IdentityT m) where
    pure x = IdentityT (pure x)
    {-# INLINE pure #-}
    fab <*> fa = IdentityT (runIdentityT fab <*> runIdentityT fa)
    {-# INLINE (<*>) #-}

instance Monad m => Monad (IdentityT m) where
    return x = IdentityT (return x)
    {-# INLINE return #-}
    ma >>= mb = IdentityT $ runIdentityT ma >>= runIdentityT . mb
    {-# INLINE (>>=) #-}

instance MonadTrans IdentityT where
    lift = IdentityT
    {-# INLINE lift #-}

instance MonadIO m => MonadIO (IdentityT m) where
    liftIO f = lift (liftIO f)
    {-# INLINE liftIO #-}

instance MonadFailure m => MonadFailure (IdentityT m) where
    type Failure (IdentityT m) = Failure m
    mFail = IdentityT . mFail

instance MonadThrow m => MonadThrow (IdentityT m) where
    throw e = IdentityT (throw e)

instance MonadCatch m => MonadCatch (IdentityT m) where
    catch (IdentityT m) c = IdentityT $ m `catch` (runIdentityT . c)
