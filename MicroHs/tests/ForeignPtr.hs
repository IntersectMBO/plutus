module ForeignPtr(main) where
import Foreign.Ptr
import Foreign.ForeignPtr
import Foreign.Storable

gc :: IO ()
gc = _primitive "IO.gc"

add :: Ptr a -> Int -> Ptr a
add = plusPtr

sInt :: Int
sInt = sizeOf (0::Int)

main :: IO ()
main = do
  fp <- mallocForeignPtrArray 2
  withForeignPtr fp $ \ p -> do
    poke p (42::Int)
    poke (add p sInt) (88::Int)
  withForeignPtr fp $ \ p -> do
    gc
    peek p >>= print
    peek (add p sInt) >>= print
  let fp1 :: ForeignPtr Int
      fp1 = plusForeignPtr fp sInt
  withForeignPtr fp1 $ \ p -> do
    peek p >>= print
  gc
