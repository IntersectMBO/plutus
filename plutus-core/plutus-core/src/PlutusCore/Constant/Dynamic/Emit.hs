{-# LANGUAGE RankNTypes #-}

module PlutusCore.Constant.Dynamic.Emit
    ( Emitter (..)
    , emitM
    ) where

import Data.Text (Text)

-- | A monad for logging that does not hardcode any concrete first-order encoding and instead packs
-- a @Monad m@ constraint and a @Text -> m ()@ argument internally, so that built-in functions that
-- do logging can work in any monad (for example, @CkM@ or @CekM@), for which there exists a
-- logging function.
newtype Emitter a = Emitter
    { unEmitter :: forall m. Monad m => (Text -> m ()) -> m a
    } deriving (Functor)

-- newtype-deriving doesn't work with 'Emitter'.
instance Applicative Emitter where
    pure x = Emitter $ \_ -> pure x
    Emitter f <*> Emitter a = Emitter $ \emit -> f emit <*> a emit

instance Monad Emitter where
    Emitter a >>= f = Emitter $ \emit -> a emit >>= \x -> unEmitter (f x) emit

emitM :: Text -> Emitter ()
emitM text = Emitter ($ text)
