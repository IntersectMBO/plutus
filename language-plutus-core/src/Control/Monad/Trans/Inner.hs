-- | Getting monad transformers out of 'Traversable' 'Monad's.

{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Control.Monad.Trans.Inner
    ( InnerT (..)
    , forBind
    , yield
    , mapInnerT
    ) where

import           Control.Monad
import           Control.Monad.Except

forBind :: (Monad m, Traversable m, Applicative f) => m a -> (a -> f (m b)) -> f (m b)
forBind a f = join <$> traverse f a

-- | Turn a 'Traversable' 'Monad' into a monad transformer.
-- > T Identity   ~ IdentityT
-- > T Maybe      ~ MaybeT
-- > T (Either e) ~ ExceptT e
-- > T ((,) w)    ~ WriterT    -- The tuple is flipped compared to the usual 'WriterT'.
newtype InnerT f m a = InnerT
    { unInnerT :: m (f a)
    }

instance (Functor f, Functor m) => Functor (InnerT f m) where
    fmap f (InnerT a) = InnerT $ fmap (fmap f) a

instance (Applicative f, Applicative m) => Applicative (InnerT f m) where
    pure = yield . pure

    InnerT f <*> InnerT a = InnerT $ (<*>) <$> f <*> a

instance (Monad f, Traversable f, Monad m) => Monad (InnerT f m) where
    InnerT m >>= f = InnerT $ do
        a <- m
        forBind a $ unInnerT . f

instance Applicative f => MonadTrans (InnerT f) where
    lift = InnerT . fmap pure

instance Monad m => MonadError () (InnerT Maybe m) where
    throwError _ = InnerT $ pure Nothing
    catchError (InnerT m) f = InnerT $ m >>= \case
        Nothing -> unInnerT $ f ()
        Just x  -> pure $ Just x

instance Monad m => MonadError e (InnerT (Either e) m) where
    throwError = InnerT . pure . Left
    catchError (InnerT m) f = InnerT $ m >>= \case
        Left e  -> unInnerT $ f e
        Right x -> pure $ Right x

-- | Embed the original 'Traversable' 'Monad' into the monad transformer that it induces.
-- The name is inspired by http://hackage.haskell.org/package/streaming-0.2.2.0/docs/Streaming.html#v:yields.
yield :: Applicative m => f a -> InnerT f m a
yield = InnerT . pure

-- | Map over the underlying representation of 'InnerT'.
mapInnerT :: (m (f a) -> n (g b)) -> InnerT f m a -> InnerT g n b
mapInnerT f (InnerT a) = InnerT (f a)
