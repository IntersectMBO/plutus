module Guard(main) where

f :: [Int] -> Int
f [x] | x < 0 = - x
      | x < 10 = x+1
      | otherwise = 99
f [x,y] = x+y
f xs | l < 4 = 0
     | otherwise = l
   where { l = length xs }

main :: IO ()
main = do
  print [f [- 7], f [5], f [20], f [2,3], f [1,2,3], f[1,2,3,4]]
