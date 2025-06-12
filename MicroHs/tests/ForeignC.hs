module ForeignC(main) where
import Foreign.C.Types
import Foreign.Ptr
import Foreign.Storable

foreign import ccall "sys/errno.h &errno" cerrno :: IO (Ptr CInt)
foreign import ccall "unistd.h getpid" getpid :: IO CInt

main :: IO ()
main = do
  CInt pid <- getpid
  print (pid /= 0)
  p <- cerrno
  CInt e <- peek p
  print e
