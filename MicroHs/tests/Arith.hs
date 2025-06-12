module Arith(module Arith) where

vals :: [Int]
vals = [-5, -2, -1, 0, 1, 2, 5]

main :: IO ()
main = do
  print [ op x y | x <- vals, y <- vals, op <- [(+),( - ),(*)] ]
  print [ op x y | x <- vals, y <- vals, y /= 0, op <- [quot, rem] ]
  print [ op x y | x <- vals, y <- vals, op <- [(==),(/=),(<),(<=),(>),(>=)] ]
  print [ op x y | x <- vals, y <- vals, let op = compare ]
