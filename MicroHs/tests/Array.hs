module Array where
import Data.Array

main :: IO ()
main = do
  let a = array (1::Int,3) [(1,'A'),(2,'b'),(3,'3')]
  let b = array (1,2) [(1,'Q'),(2,'q')]
  print a
  print (a == a)
  print (a == b)
  print $ listArray (0,4) [1..5::Int]
  print $ accumArray (+) 0 (0,1) [(1,10),(0,20),(1,5)]
  print $ a ! 1
  print $ a ! 3
  print $ bounds a
  print $ indices a
  print $ elems a
  print $ assocs a
  print $ a // [(1,'w')]
  print $ fmap fromEnum a
  print $ ixmap (0,2) succ a
