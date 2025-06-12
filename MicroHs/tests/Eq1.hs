module Eq1 where

class Eq1 f where
  eq1 :: (Eq a) => f a -> f a -> Bool

instance Eq1 Maybe where
  eq1 = (==)

main :: IO ()
main = do
  let x = Just (1::Int)
  print $ eq1 x x

