module Deriving(main) where

data T a b c = A a | B b | C a Int | D
  deriving (Eq, Ord, Show)

data Rec a = R { x :: a, y :: Int }
  deriving Show

newtype Alt f a = Alt (f a)
  deriving Show

data E = X | Y | Z
  deriving (Enum, Bounded, Show)

-- Not yet
-- data F a = F0 | F1 a | F2 (a,a) | F3 Int | F4 a Int | F5 (Int -> a)
--   deriving Functor

main :: IO ()
main = do
  print $ A 'a' == (A 'a' :: T Char () ())
  print $ A 'a' == (A 'b' :: T Char () ())
  print $ A 'a' == B False
  print $ C 'a' 1 == (C 'a' 1 :: T Char () ())
  print $ C 'a' 1 == (C 'a' 2 :: T Char () ())
  print $ D == (D :: T () () ())

  print $ A 'a' <= (A 'a' :: T Char () ())
  print $ A 'a' <= (A 'b' :: T Char () ())
  print $ A 'b' <= (A 'a' :: T Char () ())
  print $ A 'a' <= B False
  print $ C 'a' 1 <= B False

  print (A 'a' :: T Char () ())
  print (B False :: T () Bool ())
  print (C 'a' 1 :: T Char () ())
  print (D :: T () () ())
  print (A (A 'a') :: T (T Char () ()) () ())
  print $ R{ x='a', y=10 }
  print $ R{ x=R{x='b',y=11}, y=10 }

  print $ Alt [True]

  print $ fromEnum Y
  print (minBound :: E, maxBound :: E)
