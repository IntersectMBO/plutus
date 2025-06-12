module Coerce where
import Data.Coerce
import Data.Word

newtype NT = NT Int
  deriving (Show)

newtype List a = List [a]
  deriving (Show)

toInt :: (Coercible a Int) => a -> Int
toInt = coerce

toInts :: (Coercible a Int) => [a] -> [Int]
toInts = coerce

casbs :: (Coercible a b) => [a] -> [b]
casbs = coerce

class Coercible a b => MyCoercible a b
instance Coercible a b => MyCoercible a b

f :: MyCoercible a b => a -> b
f = coerce

g :: MyCoercible a Int => a -> Int
g = coerce

h :: MyCoercible b a => a -> b
h = coerce

main :: IO ()
main = do
  print (toInt (NT 5))
  print (toInts [NT 1, NT 2] :: [Int])
  print (casbs [NT 1, NT 2, NT 3] :: [Int])
  print (coerce (List [3::Int, 4]) :: [Int])
  print (coerce (List [NT 5, NT 6]) :: [NT])
  print (coerce (List [NT 7, NT 8]) :: [Int])
  print (coerce "hello" :: [Word8])
  print (f (NT 12) :: Int)
  print (g (NT 42))
  print (h (NT 24) :: Int)
