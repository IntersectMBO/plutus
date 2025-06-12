import Data.List
import System.Environment

main = do
  [pat, fn] <- getArgs
  file <- readFile fn
  let n = length $ filter (isPrefixOf pat) (tails file)
  print n

