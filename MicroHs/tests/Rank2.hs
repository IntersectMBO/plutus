module Rank2(main) where

f :: (forall a . a -> a) -> (Int, Bool)
f i = (i (1::Int), i True)

g :: (forall a . a -> Int -> a) -> (Int, Bool)
g c = (c (1::Int) (1::Int), c True (1::Int))

newtype Id = Id (forall a . a -> a)

iD :: Id
iD = Id (\ x -> x)

main :: IO ()
main = do
  print $ f id
  print $ g const
  case iD of
    Id i -> print (i (1::Int), i True)
