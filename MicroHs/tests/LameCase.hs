module LameCase where

f :: Int -> Int
f = \case
  1 -> 2
  2 -> 3
  n -> n

main :: IO ()
main = mapM_ (print . f) [1,2,3,4]
