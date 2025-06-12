module Addcombs(main) where
import Prelude
import Data.Char
import System.Environment
import System.IO

chunkify :: Int -> [Char] -> [[Char]]
chunkify n [] = []
chunkify n xs =
  let (as, bs) = splitAt n xs
  in  as : chunkify n bs

showChunk :: [Char] -> String
showChunk = concatMap (\ c -> show (ord c) ++ ",")

main :: IO ()
main = do
  args <- getArgs
  let (ifn, ofn) = case args of { [a,b] -> (a,b); _ -> error "Usage: Addcombs in-file out-file" }
  ifile <- openBinaryFile ifn ReadMode
  ofile <- openFile ofn WriteMode

  file <- hGetContents ifile
  let size = length file
      chunks = chunkify 20 file
  hPutStrLn ofile "static unsigned char combexprdata[] = {"
  mapM_ (hPutStrLn ofile . showChunk) chunks
  hPutStrLn ofile "};"
  hPutStrLn ofile "const unsigned char *combexpr = combexprdata;"
  hPutStrLn ofile $ "const int combexprlen = " ++ show size ++ ";"
--  hClose ifile
--  hClose ofile

