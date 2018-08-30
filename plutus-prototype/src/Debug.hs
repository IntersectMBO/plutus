module Debug where

import           System.IO.Unsafe

debug :: Monad m => String -> IO () -> m ()
debug n d = unsafePerformIO (putStrLn n >> d) `seq` return ()

debug_ :: Monad m => String -> m ()
debug_ n = debug n (return ())

debugSeq :: String -> a -> a
debugSeq s x = unsafePerformIO (putStrLn s) `seq` x
