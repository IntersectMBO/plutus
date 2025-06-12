module CString where

import Data.ByteString
import Foreign.C.String
import Foreign.Marshal.Alloc

main :: IO ()
main = do
    (cstr, len) <- newCStringLen "hello"
    print $ len == 5
    bs1 <- packCString cstr
    bs2 <- packCStringLen (cstr, len)
    s1 <- peekCString cstr
    s2 <- peekCStringLen (cstr, len)
    print (bs1, bs2)
    print (s1, s2)
    free cstr
    print (bs1, bs2)
    print (s1, s2)
