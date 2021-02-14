{-# LANGUAGE RankNTypes #-}

module Language.PlutusCore.Constant.Dynamic.Emit
    ( MonadEmitter (..)
    , Emitter (..)
    , NoEmitterT (..)
    ) where

import           Control.Monad.Except
import           Control.Monad.Reader
import           Control.Monad.State
import           Control.Monad.Trans.Identity

class Monad m => MonadEmitter m where
    emit :: String -> m ()

newtype Emitter a = Emitter
    { unEmitter :: forall m. MonadEmitter m => m a
    } deriving (Functor)

instance Applicative Emitter where
    pure x = Emitter $ pure x
    Emitter f <*> Emitter a = Emitter $ f <*> a

instance Monad Emitter where
    Emitter a >>= f = Emitter $ a >>= unEmitter . f

instance MonadEmitter Emitter where
    emit str = Emitter $ emit str

newtype NoEmitterT m a = NoEmitterT
    { unNoEmitterT :: m a
    } deriving
        ( Functor, Applicative, Monad
        , MonadReader r, MonadError e, MonadState s
        )
      via
        IdentityT m

instance Monad m => MonadEmitter (NoEmitterT m) where
    emit _ = pure ()
