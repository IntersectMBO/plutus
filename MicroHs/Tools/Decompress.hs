import Data.Char
import Data.Map qualified as M
import Debug.Trace
import System.Environment
import System.IO

type Table = M.Map Int [Char]

toChar :: Int -> Char
toChar i = chr (i + 32)

initTable :: Table
initTable = M.fromList $ [(c, [toChar c]) | c <- [0..94] ] ++ [(95, "\n")]

decompress :: Table -> [Int] -> [Char]
decompress t (old:is) =
  let s = t M.! old
      c = head s
  in  s ++ decompress' t old c is

decompress' :: Table -> Int -> Char -> [Int] -> [Char]
decompress' _ _ _ [] = []
decompress' _ _ _ [0] = []
decompress' t old c (n:is) =
  let s = case M.lookup n t of
            Nothing -> (t M.! old) ++ [c]
            Just x  -> x
      out = s
      c' = head s
      t' = M.insert (M.size t) (t M.! old ++ [c']) t
      old' = n
  in  out ++ decompress' t' old' c' is

fromBytes :: [Int] -> [Int]
fromBytes [] = []
fromBytes (b1:b2:b3:bs) =
  let i = b1 + 256 * b2 + 256 * 256 * b3
      i1 = i `rem` 4096
      i2 = i `quot` 4096
  in  i1 : i2 : fromBytes bs

main :: IO ()
main = do
  h <- openBinaryFile "bytes" ReadMode
  bs <- map fromEnum <$> hGetContents h
  let is = fromBytes bs
      cs = decompress initTable is
  putStr cs
