{-# LANGUAGE KindSignatures   #-}
{-# LANGUAGE TypeApplications #-}

module Bitwise.RefIO (
  MultiPtr (..),
  readAndStep,
  writeAndStep,
  RefIO,
  liftRefIO,
  runRefIO,
  )
  where

import Control.Monad.IO.Class (MonadIO (liftIO))
import Control.Monad.Primitive (PrimState)
import Control.Monad.Trans.Reader (ReaderT, ask, runReaderT)
import Data.Kind (Type)
import Data.Primitive.PrimArray (MutablePrimArray, readPrimArray, writePrimArray)
import Data.Word (Word8)
import Foreign.Ptr (Ptr, castPtr, plusPtr)
import Foreign.Storable (Storable (peek, poke, sizeOf))

newtype MultiPtr = MultiPtr (MutablePrimArray (PrimState IO) (Ptr Word8))

{-# INLINEABLE readAndStep #-}
readAndStep :: forall (a :: Type) .
  (Storable a) =>
  Int -> MultiPtr -> IO a
readAndStep ix (MultiPtr arr) = do
  let steps = sizeOf @a undefined
  p <- readPrimArray arr ix
  writePrimArray arr ix (plusPtr p steps)
  peek . castPtr $ p

{-# INLINEABLE writeAndStep #-}
writeAndStep :: forall (a :: Type) .
  (Storable a) =>
  Int -> a -> MultiPtr -> IO ()
writeAndStep ix what (MultiPtr arr) = do
  let steps = sizeOf @a undefined
  p <- readPrimArray arr ix
  poke (castPtr p) what
  writePrimArray arr ix (plusPtr p steps)

newtype RefIO (a :: Type) = RefIO (ReaderT MultiPtr IO a)
  deriving (Functor, Applicative, Monad, MonadIO) via (ReaderT MultiPtr IO)

{-# INLINEABLE liftRefIO #-}
liftRefIO :: forall (a :: Type) .
  (MultiPtr -> IO a) ->
  RefIO a
liftRefIO f = RefIO (ask >>= (liftIO . f))

{-# INLINEABLE runRefIO #-}
runRefIO :: forall (a :: Type) .
  MultiPtr -> RefIO a -> IO a
runRefIO env (RefIO comp) = runReaderT comp env
