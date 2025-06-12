module System.Directory(
  removeFile,
  doesFileExist,
  doesDirectoryExist,
  getDirectoryContents,
  listDirectory,
  setCurrentDirectory,
  getCurrentDirectory,
  withCurrentDirectory,
  createDirectory,
  createDirectoryIfMissing,
  copyFile,
  getHomeDirectory,
  ) where
import Control.Exception (bracket)
import Control.Monad (when)
import Foreign.C.String
import Foreign.Marshal.Alloc
import Foreign.Ptr
import MiniPrelude
import Prelude qualified ()
import System.Environment
import System.IO

data DIR
data Dirent

foreign import ccall "unlink"   c_unlink   :: CString -> IO Int
foreign import ccall "opendir"  c_opendir  :: CString -> IO (Ptr DIR)
foreign import ccall "closedir" c_closedir :: Ptr DIR -> IO Int
foreign import ccall "readdir"  c_readdir  :: Ptr DIR -> IO (Ptr Dirent)
foreign import ccall "c_d_name" c_d_name   :: Ptr Dirent -> IO CString
foreign import ccall "chdir"    c_chdir    :: CString -> IO Int
foreign import ccall "mkdir"    c_mkdir    :: CString -> Int -> IO Int
foreign import ccall "getcwd"   c_getcwd   :: CString -> Int -> IO CString

removeFile :: FilePath -> IO ()
removeFile fn = do
  r <- withCAString fn c_unlink
  when (r /= 0) $
    error "removeFile failed"

doesFileExist :: FilePath -> IO Bool
doesFileExist fn = do
  mh <- openFileM fn ReadMode
  case mh of
    Nothing -> return False
    Just h  -> do { hClose h; return True }

doesDirectoryExist :: FilePath -> IO Bool
doesDirectoryExist fn = withCAString fn $ \ cfn -> do
  dp <- c_opendir cfn
  if dp == nullPtr then
    return False
   else do
    c_closedir dp
    return True

getDirectoryContents :: FilePath -> IO [String]
getDirectoryContents fn = withCAString fn $ \ cfn -> do
  dp <- c_opendir cfn
  when (dp == nullPtr) $
    error $ "getDirectoryContents: cannot open " ++ fn
  let loop r = do
        de <- c_readdir dp
        if de == nullPtr then do
          c_closedir dp
          return $ reverse r
         else do
          sp <- c_d_name de
          s <- peekCAString sp
          loop (s:r)
  loop []

listDirectory :: FilePath -> IO [String]
listDirectory d = filter (\ n -> n /= "." && n /= "..") <$> getDirectoryContents d

setCurrentDirectory :: FilePath -> IO ()
setCurrentDirectory d = do
  r <- withCAString d c_chdir
  when (r /= 0) $
    error $ "setCurrentDirectory failed: " ++ d

getCurrentDirectory :: IO FilePath
getCurrentDirectory = do
  let len = 10000
  allocaBytes len $ \ p -> do
    cwd <- c_getcwd p len -- can return NULL if buffer to small
    when (cwd == nullPtr) $
      error "getCurrentDirectory"
    peekCAString cwd

withCurrentDirectory :: FilePath -> IO a -> IO a
withCurrentDirectory dir io =
  bracket getCurrentDirectory setCurrentDirectory $ \ _ -> do
    setCurrentDirectory dir
    io

createDirectory :: FilePath -> IO ()
createDirectory d = do
  r <- withCAString d $ \ s -> c_mkdir s 0o775       -- rwxrwxr-x
  when (r /= 0) $
    error $ "Cannot create directory " ++ show d

createDirectoryIfMissing :: Bool -> FilePath -> IO ()
createDirectoryIfMissing False d = do
  _ <- withCAString d $ \ s -> c_mkdir s 0o775       -- rwxrwxr-x
  return ()
createDirectoryIfMissing True d = do
  let ds = scanl1 (\ x y -> x ++ "/" ++ y) . split [] $ d
      split r []       = [r]
      split r ('/':cs) = r : split [] cs
      split r (c:cs)   = split (r ++ [c]) cs
  mapM_ (createDirectoryIfMissing False) ds

-- XXX does not copy flags
copyFile :: FilePath -> FilePath -> IO ()
copyFile src dst = do
  hsrc <- openBinaryFile src ReadMode
  hdst <- openBinaryFile dst WriteMode
  file <- hGetContents hsrc  -- this also closes the file
  hPutStr hdst file
  hClose hdst

getHomeDirectory :: IO FilePath
getHomeDirectory =
  if _isWindows then do
    user <- getEnv "USERNAME"
    return $ "C:/Users/" ++ user    -- it's a guess
  else
    getEnv "HOME"
