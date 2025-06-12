import System.Environment
import qualified Data.Map as M
import Data.Function
import Data.List

main = do
  [fn] <- getArgs
  file <- readFile fn
  let res = loop M.empty file
      loop m "" = m
      loop m cs@(_:ds) | Just (x,y) <- getComb cs = loop (M.insertWith (+) x 1 m) y
                       | otherwise = loop m ds
      getComb ('(':'$':cs) = --Just ('$':xs, tail ys) where (xs, ys) = span (/= ')') cs
        let (k1, r) = span (/= ' ') cs
        in case r of
             ' ':'$':s -> let (k2, t) = span (/= ')') s in Just ("($" ++ k1 ++ " $" ++ k2 ++ ")", tail t)
             _ -> Nothing
      getComb _ = Nothing
      srt = sortBy (compare `on` snd) $ M.toList res
  mapM print srt

