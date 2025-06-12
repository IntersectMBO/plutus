module Infix(main) where

infix 1 ===
infixl 2 +++
infixr 3 &&&

(===) :: Int -> Int -> Bool
x === y = x == y+1

(+++) :: Int -> Int -> Int
a +++ b = a + b + 1

(&&&) :: Int -> Int -> Int
a &&& b = a * (b + 1)

main :: IO ()
main = do
  print $ 2 +++ 3 &&& 4 === 17
