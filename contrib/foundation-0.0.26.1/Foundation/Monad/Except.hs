{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE CPP #-}
module Foundation.Monad.Except
    ( ExceptT(..)
    ) where

import Basement.Imports
import Foundation.Monad.Base
import Foundation.Monad.Reader
#if MIN_VERSION_base(4,13,0)
import Control.Monad.Fail
#endif

newtype ExceptT e m a = ExceptT { runExceptT :: m (Either e a) }

instance Functor m => Functor (ExceptT e m) where
    fmap f = ExceptT . fmap (fmap f) . runExceptT

instance Monad m => Applicative (ExceptT e m) where
    pure a = ExceptT $ pure (Right a)
    ExceptT f <*> ExceptT v = ExceptT $ do
        mf <- f
        case mf of
            Left e -> pure (Left e)
            Right k -> do
                mv <- v
                case mv of
                    Left e -> pure (Left e)
                    Right x -> pure (Right (k x))

instance Monad m => MonadFailure (ExceptT e m) where
    type Failure (ExceptT e m) = e
    mFail = ExceptT . pure . Left

instance Monad m => Monad (ExceptT e m) where
    return a = ExceptT $ return (Right a)
    m >>= k = ExceptT $ do
        a <- runExceptT m
        case a of
            Left e -> return (Left e)
            Right x -> runExceptT (k x)
#if !MIN_VERSION_base(4,13,0)
    fail = ExceptT . fail
#else
instance MonadFail m => MonadFail (ExceptT e m) where
    fail = ExceptT . fail
#endif

instance (Monad m, MonadFix m) => MonadFix (ExceptT e m) where
    mfix f = ExceptT (mfix (runExceptT . f . fromEither))
      where
        fromEither (Right x) = x
        fromEither (Left  _) = error "mfix (ExceptT): inner computation returned Left value"
    {-# INLINE mfix #-}

instance MonadReader m => MonadReader (ExceptT e m) where
    type ReaderContext (ExceptT e m) = ReaderContext m
    ask = ExceptT (Right <$> ask)

instance MonadTrans (ExceptT e) where
    lift f = ExceptT (Right <$> f)

instance MonadIO m => MonadIO (ExceptT e m) where
    liftIO f = ExceptT (Right <$> liftIO f)
