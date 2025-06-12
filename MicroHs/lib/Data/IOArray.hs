module Data.IOArray(module Data.IOArray, IOArray) where
import qualified Prelude()              -- do not import Prelude
import Primitives

-- data IOArray

newIOArray :: forall a . Int -> a -> IO (IOArray a)
newIOArray = primArrAlloc

sizeIOArray :: forall a . IOArray a -> IO Int
sizeIOArray = primArrSize

readIOArray :: forall a . IOArray a -> Int -> IO a
readIOArray = primArrRead

writeIOArray :: forall a . IOArray a -> Int -> a -> IO ()
writeIOArray = primArrWrite
