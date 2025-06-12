module Enum(main) where

import Data.Int
import Data.Word
import Numeric.Natural

data T = A | B | C
  deriving (Bounded, Enum, Show)

printEnumInt :: forall a. (Bounded a, Enum a, Num a, Show a) => IO ()
printEnumInt = do
  print $ enumFrom @a maxBound
  print $ enumFromThen @a (maxBound - 2) maxBound
  print $ enumFromTo @a (maxBound - 2) maxBound
  print $ enumFromThenTo @a (maxBound - 5) (maxBound - 3) maxBound

main :: IO ()
main = do
  -- derived instance
  print $ succ A
  print $ succ B
  print $ pred B
  print $ pred C
  print $ map (toEnum @T) [0, 1, 2]
  print $ map fromEnum [A, B, C]
  print [A ..]
  print [A, C ..]
  print [C, A ..]
  print [A, B .. C]
  print [C, B .. A]
  print ([minBound .. maxBound] :: [T])

  -- Bool
  print [False ..]
  print [False, True ..]

  -- Ordering
  print [LT ..]
  print [LT, EQ ..]

  -- Char
  let maxChar = maxBound :: Char
  print [maxChar ..]
  print [pred maxChar, maxChar ..]

  -- Int, Word
  printEnumInt @Int8
  printEnumInt @Int16
  printEnumInt @Int32
  printEnumInt @Word8
  printEnumInt @Word16
  printEnumInt @Word32

  -- Natural
  let bigInt = 2 ^ 64 :: Natural
  print [bigInt..bigInt+2]
  print $ take 3 [bigInt..]
  print [bigInt-2, bigInt..bigInt+2]
  print $ take 3 [bigInt-2, bigInt..]
  print [10 :: Natural, 5..]
