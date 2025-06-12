module ListTest(module ListTest) where

import Data.List

main :: IO ()
main = do
  print $ sum [1, 2, 3 :: Int]
  print $ product [1, 2, 3, 4 :: Int]
  print $ and [True]
  print $ and [True, False]
  print $ [2] `isInfixOf` [1, 2, 3 :: Int]
