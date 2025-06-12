-- Copyright 2023 Lennart Augustsson
-- See LICENSE file for full license.
module System.Environment(
  getArgs,
  getProgName,
  withArgs,
  lookupEnv,
  getEnv,
  ) where
import Foreign.C.String
import Foreign.Ptr
import MiniPrelude
import Prelude qualified ()
import Primitives
import System.IO

-- primArgRef returns an array containing a list of strings.
-- The first element is the program name, the rest are the arguments.
getArgs :: IO [String]
getArgs = do
  aa <- primGetArgRef
  as <- primArrRead aa 0
  return $ tail as                          -- drop program name

getProgName :: IO String
getProgName = do
  aa <- primGetArgRef
  as <- primArrRead aa 0
  return $ head as                          -- get program name

withArgs :: forall a . [String] -> IO a -> IO a
withArgs as ioa = do
  aa <- primGetArgRef
  old <- primArrRead aa 0
  primArrWrite aa 0 $ head old : as         -- keep program name
  a <- ioa
  primArrWrite aa 0 old
  return a

foreign import ccall "getenv" c_getenv :: CString -> IO CString

lookupEnv :: String -> IO (Maybe String)
lookupEnv var = do
  cptr <- withCAString var c_getenv
  if cptr == nullPtr then
    return Nothing
   else
    Just <$> peekCAString cptr

getEnv :: String -> IO String
getEnv var = do
  mval <- lookupEnv var
  case mval of
    Nothing  -> error $ "getEnv: not found " ++ var
    Just val -> return val
