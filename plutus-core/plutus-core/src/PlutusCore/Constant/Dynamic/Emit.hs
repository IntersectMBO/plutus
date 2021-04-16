{-# LANGUAGE RankNTypes #-}

module PlutusCore.Constant.Dynamic.Emit
    ( MonadEmitter (..)
    , Emitter (..)
    , NoEmitterT (..)
    ) where

import           Control.Monad.Except
import           Control.Monad.Reader
import           Control.Monad.State
import           Control.Monad.Trans.Identity

-- | A class for emitting 'String's in a monadic context (basically, for logging).
class Monad m => MonadEmitter m where
    emit :: String -> m ()

-- | A concrete type implementing 'MonadEmitter'. Useful in signatures of built-in functions that
-- do logging. We don't use any concrete first-order encoding and instead pack a @MonadEmitter m@
-- constraint internally, so that built-in functions that do logging can work in any monad
-- implementing 'MonadEmitter' (for example, @CkM@ or @CekM@).
newtype Emitter a = Emitter
    { unEmitter :: forall m. MonadEmitter m => m a
    } deriving (Functor)

-- newtype-deriving doesn't work with 'Emitter'.
instance Applicative Emitter where
    pure x = Emitter $ pure x
    Emitter f <*> Emitter a = Emitter $ f <*> a

instance Monad Emitter where
    Emitter a >>= f = Emitter $ a >>= unEmitter . f

instance MonadEmitter Emitter where
    emit str = Emitter $ emit str

-- | A newtype wrapper for via-deriving a vacuous 'MonadEmitter' instance for a monad.
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

instance (MonadEmitter m) => MonadEmitter (ExceptT e m) where
    emit = lift . emit
