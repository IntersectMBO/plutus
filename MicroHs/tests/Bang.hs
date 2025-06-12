module Bang where

(!) :: Int -> Int -> Int
x ! y = x - y

f :: Int -> Int
f !x = x+1

main = do
  let !a = 1+2
  print a
  print (2 ! 3)
  print (2! 3)
  print (2 !3)
  print (2!3)
  print (f 1)
