module Data.IORef(
  IORef,
  newIORef,
  readIORef,
  writeIORef,
  modifyIORef,
  atomicModifyIORef,
  ) where
import Data.Eq
import {-# SOURCE #-} Data.Typeable
import Prelude qualified ()
import Primitives

-- An IORef is represented as an IOArray with a single element.
newtype IORef a = R (IOArray a)
  deriving (Typeable)

instance Eq (IORef a) where
  R x == R y  =  primArrEQ x y

newIORef :: forall a . a -> IO (IORef a)
newIORef a = primArrAlloc 1 a `primBind` \ p -> primReturn (R p)

readIORef :: forall a . IORef a -> IO a
readIORef (R p) = primArrRead p 0

writeIORef :: forall a . IORef a -> a -> IO ()
writeIORef (R p) a = primArrWrite p 0 a

modifyIORef :: forall a . IORef a -> (a -> a) -> IO ()
modifyIORef (R p) f = primArrRead p 0 `primBind` \ a -> primArrWrite p 0 (f a)

-- XXX WRONG
atomicModifyIORef :: forall a b . IORef a -> (a -> (a, b)) -> IO b
atomicModifyIORef r f = readIORef r `primBind` \ a -> let (a', b) = f a in writeIORef r a' `primThen` primReturn b
