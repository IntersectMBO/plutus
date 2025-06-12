module Foreign.Marshal.Utils(module Foreign.Marshal.Utils) where
import qualified Prelude(); import MiniPrelude
import Foreign.Marshal.Alloc
import Foreign.C.Types
import Foreign.Ptr
import Foreign.Storable

new :: forall a . Storable a => a -> IO (Ptr a)
new val = do
  ptr <- malloc
  poke ptr val
  return ptr

with :: forall a b . Storable a => a -> (Ptr a -> IO b) -> IO b
with val f  =
  alloca $ \ ptr -> do
    poke ptr val
    f ptr

fromBool :: forall a . Num a => Bool -> a
fromBool False = 0
fromBool True  = 1

toBool :: forall a . (Eq a, Num a) => a -> Bool
toBool = (/= 0)

maybeNew :: forall a b .
            (      a -> IO (Ptr b))
         -> (Maybe a -> IO (Ptr b))
maybeNew  = maybe (return nullPtr)

maybeWith :: forall a b c .
             (      a -> (Ptr b -> IO c) -> IO c)
          -> (Maybe a -> (Ptr b -> IO c) -> IO c)
maybeWith  = maybe ($ nullPtr)

maybePeek :: forall a b . (Ptr a -> IO b) -> Ptr a -> IO (Maybe b)
maybePeek peek ptr | ptr == nullPtr  = return Nothing
                   | otherwise       = do { a <- peek ptr; return (Just a) }

withMany :: forall a b res .
            (a -> (b -> res) -> res)
         -> [a]
         -> ([b] -> res)
         -> res
withMany _   []       f = f []
withMany wth (x : xs) f =
  wth x $ \ x' ->
    withMany wth xs (\ xs' -> f (x' : xs'))

foreign import ccall "memcpy"  c_memcpy  :: Ptr () -> Ptr () -> CSize -> IO ()
foreign import ccall "memmove" c_memmove :: Ptr () -> Ptr () -> CSize -> IO ()

copyBytes :: forall a b . Ptr a -> Ptr a -> Int -> IO ()
copyBytes p q i = c_memcpy (castPtr p) (castPtr q) (intToCSize i)

moveBytes :: forall a b . Ptr a -> Ptr a -> Int -> IO ()
moveBytes p q i = c_memmove (castPtr p) (castPtr q) (intToCSize i)
