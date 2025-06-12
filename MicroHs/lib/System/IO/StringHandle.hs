module System.IO.StringHandle(handleWriteToString, stringToHandle) where
import Prelude; import MiniPrelude
import Foreign.C.String
import Foreign.C.Types
import Foreign.Marshal.Alloc
import Foreign.Marshal.Utils
import Foreign.Ptr
import Foreign.Storable
import System.IO
import System.IO.Internal

foreign import ccall "openb_wr_buf"          c_openb_wr_buf          :: IO (Ptr BFILE)
foreign import ccall "openb_rd_buf"          c_openb_rd_buf          :: CString -> Int -> IO (Ptr BFILE)
foreign import ccall "get_buf"               c_get_buf               :: Ptr BFILE -> Ptr CString -> Ptr Int -> IO ()

-- Turn all writes to a Handle into a String.
-- Do not close the Handle in the action
handleWriteToString :: (Handle -> IO ()) -> IO String
handleWriteToString act = do
  bf <- c_openb_wr_buf                         -- create a buffer
  h <- mkHandle "handleToString" bf HWrite
  act h
  hFlush h
  with nullPtr $ \ bufp ->
    with 0 $ \ lenp -> do
      c_get_buf bf bufp lenp                   -- get buffer and length
      buf <- peek bufp
      len <- peek lenp
      res <- peekCAStringLen (buf, len)        -- encode as a string
      free buf                                 -- free owned memory
      hClose h                                 -- close
      return res

-- Make a Handle that will read from a String.
-- Caller should close the Handle.
stringToHandle :: String -> IO Handle
stringToHandle file = do
  (ptr, len) <- newCAStringLen file            -- make memory buffer
  bf <- c_openb_rd_buf ptr len                 -- open it for reading
  mkHandle "stringToHandle" bf HRead           -- and make a handle
