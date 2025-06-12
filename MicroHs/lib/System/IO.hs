-- Copyright 2023,2024 Lennart Augustsson
-- See LICENSE file for full license.
module System.IO(
  IO, Handle, FilePath,
  IOMode(..),
  stdin, stdout, stderr,
  hGetChar, hPutChar,
  hLookAhead,
  putChar, getChar,
  hClose, hFlush,
  openFile, openFileM, openBinaryFile,
  hPutStr, hPutStrLn,
  putStr, putStrLn,
  print,
  hGetContents, getContents,
  hGetLine, getLine,
  interact,
  writeFile, readFile, appendFile,

  cprint, cuprint,

  mkTextEncoding, hSetEncoding, utf8,

  openTmpFile, openTempFile, openBinaryTempFile,

  withFile,

  BufferMode(..),
  hSetBuffering,

  IOException(..),

  ) where
import Control.Applicative
import Control.Error
import Control.Exception.Internal (bracket)
import Control.Monad
import Control.Monad.Fail
import Data.Bool
import Data.Char
import Data.Eq
import Data.Function
import Data.Functor
import Data.Int
import Data.List
import Data.Maybe
import Data.Num
import Data.Ord
import Data.String
import Data.Tuple
import Foreign.C.String
import Foreign.Marshal.Alloc
import Foreign.Ptr
import Prelude qualified ()
import Primitives
import System.IO.Error
import System.IO.Internal
import System.IO.Unsafe
import Text.Show

data FILE

primHPrint       :: forall a . Ptr BFILE -> a -> IO ()
primHPrint        = _primitive "IO.print"
primStdin        :: ForeignPtr BFILE
primStdin         = _primitive "IO.stdin"
primStdout       :: ForeignPtr BFILE
primStdout        = _primitive "IO.stdout"
primStderr       :: ForeignPtr BFILE
primStderr        = _primitive "IO.stderr"

foreign import ccall "fopen"        c_fopen        :: CString -> CString -> IO (Ptr FILE)
foreign import ccall "closeb"       c_closeb       :: Ptr BFILE          -> IO ()
foreign import ccall "flushb"       c_flushb       :: Ptr BFILE          -> IO ()
foreign import ccall "getb"         c_getb         :: Ptr BFILE          -> IO Int
foreign import ccall "ungetb"       c_ungetb       :: Int -> Ptr BFILE   -> IO ()
foreign import ccall "putb"         c_putb         :: Int -> Ptr BFILE   -> IO ()
foreign import ccall "add_FILE"     c_add_FILE     :: Ptr FILE           -> IO (Ptr BFILE)
foreign import ccall "add_utf8"     c_add_utf8     :: Ptr BFILE          -> IO (Ptr BFILE)

----------------------------------------------------------

stdin  :: Handle
stdin  = unsafeHandle primStdin  HRead  "stdin"
stdout :: Handle
stdout = unsafeHandle primStdout HWrite "stdout"
stderr :: Handle
stderr = unsafeHandle primStderr HWrite "stderr"

--bFILE :: Ptr FILE -> Handle
--bFILE = Handle . primPerformIO . (c_add_utf8 <=< c_add_FILE)

hClose :: Handle -> IO ()
hClose h =
  -- Don't close the std handles, the runtime assume they remain open.
  if h == stdin then
    return ()
  else if h == stdout || h == stderr then
    hFlush h       -- closing would have flushed
  else
    hCloseReal h

hCloseReal :: Handle -> IO ()
hCloseReal h = do
  m <- getHandleState h
  case m of
    HClosed -> return ()
    HSemiClosed -> return ()
    _ -> do
      killHandle h
      withHandleAny h c_closeb
  setHandleState h HClosed

hFlush :: Handle -> IO ()
hFlush h = withHandleWr h c_flushb

hGetChar :: Handle -> IO Char
hGetChar h = withHandleRd h $ \ p -> do
  c <- c_getb p
  if c == (-1::Int) then
    ioErrH h EOF "hGetChar"
  else if c `primIntAnd` 0x1ff800 == 0xd800 then
    ioErrH h InvalidArgument "hGetChar: surrogate"
  else
    return (chr c)

hLookAhead :: Handle -> IO Char
hLookAhead h = withHandleRd h $ \ p -> do
  c <- hGetChar h
  c_ungetb (ord c) p
  return c

hPutChar :: Handle -> Char -> IO ()
hPutChar h c
  | i `primIntAnd` 0x1ff800 == 0xd800 = ioErrH h InvalidArgument "hPutChar: surrogate"
  | otherwise = withHandleWr h $ c_putb i
  where i = ord c

openFILEM :: FilePath -> IOMode -> IO (Maybe (Ptr FILE))
openFILEM p m = do
  let
    ms = case m of
          ReadMode      -> "r"
          WriteMode     -> "w"
          AppendMode    -> "a"
          ReadWriteMode -> "w+"
  h <- withCAString p $ \cp -> withCAString ms $ \ cm -> c_fopen cp cm
  if h == nullPtr then
    return Nothing
   else
    return (Just h)

openFileM :: FilePath -> IOMode -> IO (Maybe Handle)
openFileM fn m = do
  mf <- openFILEM fn m
  case mf of
    Nothing -> return Nothing
    Just p  -> do { q <- c_add_utf8 =<< c_add_FILE p; Just <$> mkHandle fn q (ioModeToHMode m) }

openFile :: String -> IOMode -> IO Handle
openFile p m = do
  mh <- openFileM p m
  case mh of
    Nothing -> ioErr NoSuchThing "openFile" p
    Just h  -> return h

putChar :: Char -> IO ()
putChar = hPutChar stdout

getChar :: IO Char
getChar = hGetChar stdin

cprint :: forall a . a -> IO ()
cprint a = withHandleWr stdout $ \ p ->
  primRnfNoErr a `seq`
  primGC `primThen`     -- Do GC reductions
  primGC `primThen`
  primGC `primThen`
  primGC `primThen`
  primGC `primThen`
  primGC `primThen`
  primHPrint p a

cuprint :: forall a . a -> IO ()
cuprint a = withHandleWr stdout $ \ p -> primHPrint p a

print :: forall a . (Show a) => a -> IO ()
print a = putStrLn (show a)

putStr :: String -> IO ()
putStr = hPutStr stdout

hPutStr :: Handle -> String -> IO ()
hPutStr h = mapM_ (hPutChar h)

putStrLn :: String -> IO ()
putStrLn = hPutStrLn stdout

hPutStrLn :: Handle -> String -> IO ()
hPutStrLn h s = hPutStr h s >> hPutChar h '\n'

hGetLine :: Handle -> IO String
hGetLine h = loop ""
  where loop s = do
          c <- hGetChar h
          if c == '\n' then
            return (reverse s)
           else
            loop (c:s)

getLine :: IO String
getLine = hGetLine stdin

writeFile :: FilePath -> String -> IO ()
writeFile p s = do
  h <- openFile p WriteMode
  hPutStr h s
  hClose h

appendFile :: FilePath -> String -> IO ()
appendFile p s = do
  h <- openFile p AppendMode
  hPutStr h s
  hClose h

{-
-- Faster, but uses a lot more C memory.
writeFileFast :: FilePath -> String -> IO ()
writeFileFast p s = do
  h <- openFile p WriteMode
  (cs, l) <- newCAStringLen s
  n <- c_fwrite cs 1 l h
  free cs
  hClose h
  when (l /= n) $
    error "writeFileFast failed"
-}

-- Lazy readFile
readFile :: FilePath -> IO String
readFile p = do
  h <- openFile p ReadMode
  hGetContents h  --  can't close with lazy hGetContents

-- Lazy hGetContents
hGetContents :: Handle -> IO String
hGetContents h = withHandleRd h $ \ p -> do
  c <- c_getb p
  if c == (-1::Int) then do
    hClose h                           -- EOF, so close the handle
    setHandleState h HSemiClosed       -- but still allow a regular close
    return ""
  else if c `primIntAnd` 0x1ff800 == 0xd800 then
    ioErrH h InvalidArgument "hGetContents: surrogate"
  else do
    cs <- unsafeInterleaveIO (hGetContents h)
    return (chr c : cs)

getContents :: IO String
getContents = hGetContents stdin

interact :: (String -> String) -> IO ()
interact f = getContents >>= putStr . f

openBinaryFile :: String -> IOMode -> IO Handle
openBinaryFile fn m = do
  mf <- openFILEM fn m
  case mf of
    Nothing -> ioErr NoSuchThing "openBinaryFile" fn
    Just p  -> do { q <- c_add_FILE p; mkHandle fn q (ioModeToHMode m) }

--------

ioErrH :: Handle -> IOErrorType -> String -> IO a
ioErrH h typ desc   = ioError $ IOError (Just h) typ "" desc Nothing Nothing

ioErr :: IOErrorType -> String -> String -> IO a
ioErr typ desc name = ioError $ IOError Nothing  typ "" "" Nothing (Just $ name ++ ": " ++ desc)

--------
-- For compatibility

data TextEncoding = UTF8

utf8 :: TextEncoding
utf8 = UTF8

mkTextEncoding :: String -> IO TextEncoding
mkTextEncoding "UTF-8//ROUNDTRIP" = return UTF8
mkTextEncoding _                  = error "unknown text encoding"

-- Always in UTF8 mode
hSetEncoding :: Handle -> TextEncoding -> IO ()
hSetEncoding _ _ = return ()

--------

withFile :: forall r . FilePath -> IOMode -> (Handle -> IO r) -> IO r
withFile fn md io = bracket (openFile fn md) hClose io

withBinaryFile :: forall r . FilePath -> IOMode -> (Handle -> IO r) -> IO r
withBinaryFile fn md io = bracket (openBinaryFile fn md) hClose io

--------

splitTmp :: String -> (String, String)
splitTmp tmpl =
  case span (/= '.') (reverse tmpl) of
    (rsuf, "")     -> (tmpl, "")
    (rsuf, _:rpre) -> (reverse rpre, '.':reverse rsuf)

-- Create a temporary file, take a prefix and a suffix
-- and returns a malloc()ed string.
foreign import ccall "tmpname" c_tmpname :: CString -> CString -> IO CString

-- Create and open a temporary file.
openTmpFile :: String -> IO (String, Handle)
openTmpFile tmpl = do
  let (pre, suf) = splitTmp tmpl
  ctmp <- withCAString pre $ withCAString suf . c_tmpname
  tmp <- peekCAString ctmp
  free ctmp
  h <- openFile tmp ReadWriteMode
  return (tmp, h)

-- Sloppy implementation of openTempFile
openTempFile' :: (FilePath -> IOMode -> IO Handle) -> FilePath -> String -> IO (String, Handle)
openTempFile' open tmp tmplt = do
  let (pre, suf) = splitTmp tmplt
      loop n = do
        let fn = tmp ++ "/" ++ pre ++ show n ++ suf
        mh <- openFileM fn ReadMode
        case mh of
          Just h -> do
            hClose h
            loop (n+1 :: Int)
          Nothing -> do
            h <- open fn ReadWriteMode
            return (fn, h)
  loop 0

openTempFile :: FilePath -> String -> IO (String, Handle)
openTempFile = openTempFile' openFile

openBinaryTempFile :: FilePath -> String -> IO (String, Handle)
openBinaryTempFile = openTempFile' openBinaryFile

data BufferMode = NoBuffering | LineBuffering | BlockBuffering (Maybe Int)
  deriving (Eq, Ord, Show)

-- This currently does nothing.
hSetBuffering :: Handle -> BufferMode -> IO ()
hSetBuffering _ _ = return ()
