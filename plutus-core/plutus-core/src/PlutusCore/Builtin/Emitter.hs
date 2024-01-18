module PlutusCore.Builtin.Emitter
    ( Emitter (..)
    , runEmitter
    , MonadEmitter (..)
    ) where

import Control.Monad.Trans.Writer.Strict (Writer, runWriter, tell)
import Data.DList as DList
import Data.Text (Text)

-- | A monad for logging.
newtype Emitter a = Emitter
    { unEmitter :: Writer (DList Text) a
    } deriving newtype (Functor, Applicative, Monad)

runEmitter :: Emitter a -> (a, DList Text)
runEmitter = runWriter . unEmitter
{-# INLINE runEmitter #-}

-- | A type class for \"this monad supports logging\".
class MonadEmitter m where
    emit :: Text -> m ()

instance MonadEmitter Emitter where
    emit = Emitter . tell . pure
    {-# INLINE emit #-}
