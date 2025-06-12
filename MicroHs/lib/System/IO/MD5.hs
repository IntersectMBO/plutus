-- Copyright 2023 Lennart Augustsson
-- See LICENSE file for full license.
module System.IO.MD5(MD5CheckSum, md5File, md5Handle, md5String, md5Combine) where
import Control.DeepSeq.Class
import Data.Coerce
import Data.Word
import Foreign.C.String
import Foreign.Marshal.Alloc
import Foreign.Marshal.Array
import Foreign.Ptr
import MiniPrelude
import Prelude qualified ()
import Primitives (primPerformIO)
import System.IO
import System.IO.Internal

foreign import ccall "md5BFILE"  c_md5BFILE  :: Ptr BFILE -> Ptr Word -> IO ()
foreign import ccall "md5String" c_md5String :: CString   -> Ptr Word -> IO ()
foreign import ccall "md5Array"  c_md5Array  :: Ptr Word  -> Ptr Word -> Int -> IO ()

newtype MD5CheckSum = MD5 [Word]  -- either 2*64 bits or 4*32 bits
  deriving (Eq, Ord)

instance Show MD5CheckSum where
  show (MD5 ws) = "MD5" ++ show ws

instance NFData MD5CheckSum where
  rnf (MD5 ws) = rnf ws

md5Len :: Int
md5Len = 16   -- The MD5 checksum is 16 bytes

md5WLen :: Int  -- length in words
md5WLen = (md5Len * 8) `quot` _wordSize

chksum :: (Ptr Word -> IO ()) -> IO MD5CheckSum
chksum fn = do
  buf <- mallocArray md5WLen
  fn buf
  wmd5 <- peekArray md5WLen buf
  free buf
  return (MD5 wmd5)

md5String :: String -> MD5CheckSum
md5String s = primPerformIO $ withCAString s $ chksum . c_md5String

md5Handle :: Handle -> IO MD5CheckSum
md5Handle h = withHandleRd h $ chksum . c_md5BFILE

md5File :: FilePath -> IO (Maybe MD5CheckSum)
md5File fn = do
  mh <- openFileM fn ReadMode
  case mh of
    Nothing -> return Nothing
    Just h -> do
      cs <- md5Handle h
      hClose h
      return (Just cs)

md5Combine :: [MD5CheckSum] -> MD5CheckSum
md5Combine [] = error "md5Combine: empty"
md5Combine [m] = m
md5Combine ms = primPerformIO $
  withArrray [ w | MD5 ws <- ms, w <- ws ] $ \ a ->
    chksum $ \ w -> c_md5Array a w (length ms * md5Len)
