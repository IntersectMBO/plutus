module Data.Text.IO (
  -- * File-at-a-time operations
  readFile,
  writeFile,
  appendFile,
  -- * Operations on handles
  hGetContents,
  hGetChunk,
  hGetLine,
  hPutStr,
  hPutStrLn,
  -- * Special cases for standard input and output
  interact,
  getContents,
  getLine,
  putStr,
  putStrLn,
) where

import Control.Exception (evaluate)
import Data.ByteString qualified as BS
import Data.Text
import Data.Text.Encoding
import Prelude hiding (readFile, writeFile)
import Prelude qualified as P
import System.IO qualified as IO
import System.IO (Handle, IOMode (..), hClose, openFile, stdin, stdout)

readFile :: FilePath -> IO Text
readFile f = do
  h <- openFile f ReadMode
  hGetContents h

writeFile :: FilePath -> Text -> IO ()
writeFile f bs = do
  h <- openFile f WriteMode
  hPutStr h bs
  hClose h

appendFile :: FilePath -> Text -> IO ()
appendFile f bs = do
  h <- openFile f AppendMode
  hPutStr h bs
  hClose h

hGetContents :: Handle -> IO Text
hGetContents h = do
  bs <- BS.hGetContents h
  evaluate (decodeUtf8 bs)

hGetChunk :: Handle -> IO Text
hGetChunk = hGetContents -- XXX: read chunk from buffer

hGetLine :: Handle -> IO Text
hGetLine h = do
  bs <- BS.hGetLine h
  evaluate (decodeUtf8 bs)

hPutStr :: Handle -> Text -> IO ()
hPutStr h t = BS.hPutStr h (encodeUtf8 t)

hPutStrLn :: Handle -> Text -> IO ()
hPutStrLn h t = hPutStr h t >> hPutStr h (pack "\n")

interact :: (Text -> Text) -> IO ()
interact f = getContents >>= putStr . f

getContents :: IO Text
getContents = hGetContents stdin

getLine :: IO Text
getLine = hGetLine stdin

putStr :: Text -> IO ()
putStr = hPutStr stdout

putStrLn :: Text -> IO ()
putStrLn = hPutStrLn stdout
