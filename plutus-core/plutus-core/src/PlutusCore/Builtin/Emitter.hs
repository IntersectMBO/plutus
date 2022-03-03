module PlutusCore.Builtin.Emitter
    ( Emitter (..)
    , runEmitter
    , emit
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

emit :: Text -> Emitter ()
emit = Emitter . tell . pure
{-# INLINE emit #-}
