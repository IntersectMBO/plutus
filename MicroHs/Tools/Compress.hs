module Compress(main) where
import Prelude
import Data.Map as M
import Data.Char
import System.Environment
import System.IO
--import Debug.Trace

--
-- A simple LZW compressor
-- It uses a dictionary of maximum size 4096.
-- The 12 bit code words are encoded with 2 code words in 3 bytes.
-- It can only compress input of printable ASCII + '\n'

type Table = M.Map [Char] Int

-- Don't change this lightly.
-- It needs to be coordinated with the decompressor transducer in eval.c
maxDict :: Int
maxDict = 4096

toChar :: Int -> Char
toChar i = chr (i + 32)

(!) :: Table -> [Char] -> Int
(!) t s =
  case M.lookupBy compare s t of
    Nothing -> undefined -- error $ "(!): " ++ showString s
    Just i -> i

compress :: Table -> [Char] -> [Char] -> [Int]
compress t [] p = [ t ! p ]
compress t (c:cs) p =
  let p' = p ++ [c]
      s = M.size t
      t' = if s < maxDict then M.insertBy compare p' s t else t
  in
--      trace ("compress " ++ showString p') $
--      trace show (M.toList t)) $
      case M.lookupBy compare p' t of
        Just _ ->
--          trace "found" $
          compress t cs p'
        Nothing ->
--          trace ("not found p=" ++ show p ++ " " ++ show (M.lookupBy compare p t)) $
          (t ! p) : compress t' cs [c]

-- Initial table is ' ' .. '~', and '\n'
initTable :: Table
initTable = M.fromListBy compare $ [([toChar c], c) | c <- [0..94] ] ++ [("\n", 95)]

toBytes :: [Int] -> [Int]
toBytes [] = []
toBytes [i] = [i `rem` 256, i `quot` 256, 0]
toBytes (i1:i2:is) =
  let i = i1 + 4096*i2
      b1 = i `rem` 256
      b2 = (i `quot` 256) `rem` 256
      b3 = i `quot` (256*256)
  in  b1 : b2 : b3 : toBytes is

bad :: Char -> Bool
bad c = not (isPrint c || c == '\n')

main :: IO ()
main = do
  args <- getArgs
  let (ifn, ofn) = case args of { [a,b] -> (a,b); _ -> error "Usage: Compress in-file out-file" }
  ifile <- openFile ifn ReadMode
  f <- hGetContents ifile
  when (any bad f) $
    error "Non-printable ASCII in input"
  let bs = compress initTable f []
  ofile <- openBinaryFile ofn WriteMode
  hPutStr ofile $ 'Z' : map chr (toBytes bs)
  hClose ifile
  hClose ofile
