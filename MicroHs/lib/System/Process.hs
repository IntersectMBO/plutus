module System.Process(callCommand) where
import Control.Monad (when)
import Foreign.C.String
import MiniPrelude
import Prelude qualified ()

foreign import ccall "system" systemc :: CString -> IO Int

callCommand :: String -> IO ()
callCommand cmd = do
  r <- withCAString cmd systemc
  when (r /= 0) $
    error $ "callCommand: failed " ++ show r ++ ", " ++ show cmd
