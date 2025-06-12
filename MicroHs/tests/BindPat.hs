module BindPat(main) where

foo :: [Int] -> [Int]
foo xs = do
  1 <- xs
  pure 2

main :: IO ()
main = do
  print $ foo [1,1]
  print $ foo [2]
