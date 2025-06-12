module MultiIf where

f :: Int -> Int
f x =
  let (a, b) | x == 0 = (2,3)
             | otherwise = (3, 4)
      (c, d) = (10, 11)
  in  a*c + b*d

g :: Int -> Int
g x =
  if { | x <  0 -> -1
     ; | x == 0 -> 0
     ; | x >  0 -> 1 }

h :: Int -> Int
h x =
  if | x <  0 -> if | x < -10   -> -2
                    | otherwise -> -1
     | x == 0 -> 0
     | x >  0 -> 1

main :: IO ()
main = do
  print (f 0)
  print (f 1)
  print (g 100)
  print (g 0)
  print (g (-5))
  print (h (-100))
  print (h (-2))
  print (h 0)
  print (h 100)
