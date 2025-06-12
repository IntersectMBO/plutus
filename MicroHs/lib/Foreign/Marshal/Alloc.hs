module Foreign.Marshal.Alloc(
  malloc, calloc, alloca,
  free,
  mallocBytes, callocBytes, allocaBytes,
  ) where
import Control.Error (undefined)
import Foreign.C.Types
import Foreign.Ptr
import Foreign.Storable
import Prelude qualified ()
import Primitives

foreign import ccall "free" c_free :: Ptr () -> IO ()

free :: forall a . Ptr a -> IO ()
free p = c_free (castPtr p)

foreign import ccall "malloc" c_malloc :: CSize -> IO (Ptr ())

mallocBytes :: forall a . Int -> IO (Ptr a)
mallocBytes n = c_malloc (intToCSize n) `primBind` \ p -> primReturn (castPtr p)

foreign import ccall "calloc" c_calloc :: CSize -> CSize -> IO (Ptr ())

callocBytes :: forall a . Int -> IO (Ptr a)
callocBytes n = c_calloc (intToCSize (1::Int)) (intToCSize n) `primBind` \ p -> primReturn (castPtr p)

malloc :: forall a . Storable a => IO (Ptr a)
malloc  = mallocBytes (sizeOf (undefined :: a))

calloc :: forall a . Storable a => IO (Ptr a)
calloc = callocBytes (sizeOf (undefined :: a))

alloca :: forall a b . Storable a => (Ptr a -> IO b) -> IO b
alloca = allocaBytes (sizeOf (undefined :: a))

allocaBytes :: forall a b . Int -> (Ptr a -> IO b) -> IO b
allocaBytes len io =
  mallocBytes len `primBind` (\ p ->
  io p `primBind` (\ b ->
  free p `primThen`
  primReturn b))
