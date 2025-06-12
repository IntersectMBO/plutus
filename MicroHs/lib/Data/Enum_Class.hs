module Data.Enum_Class(Enum(..)) where
import Control.Error
import Data.Bool
import Data.Function ((.))
import Data.List_Type
import Prelude qualified ()
import Primitives

class Enum a where
  succ           :: a -> a
  pred           :: a -> a
  toEnum         :: Int -> a
  fromEnum       :: a -> Int

  enumFrom       :: a -> [a]
  enumFromThen   :: a -> a -> [a]
  enumFromTo     :: a -> a -> [a]
  enumFromThenTo :: a -> a -> a -> [a]

  succ                   = toEnum . primIntAdd 1 . fromEnum
  pred                   = toEnum . primIntSubR 1 . fromEnum
  enumFrom x             = [ toEnum i | i <- [fromEnum x ..] ]
  enumFromThen x y       = [ toEnum i | i <- [fromEnum x, fromEnum y ..] ]
  enumFromTo x y         = [ toEnum i | i <- [fromEnum x .. fromEnum y] ]
  enumFromThenTo x1 x2 y = [ toEnum i | i <- [fromEnum x1, fromEnum x2 .. fromEnum y] ]

eftInt :: Int -> Int -> [Int]
eftInt x y = if x `primIntGT` y then [] else go x
  where
    go n = n : if n `primIntEQ` y then [] else go (n `primIntAdd` 1)

efttIntUp :: Int -> Int -> Int -> [Int]
-- x2 >= x1
efttIntUp x1 x2 y
  | y `primIntLT` x2 = if y `primIntLT` x1 then [] else [x1]
  | otherwise =
    let
      delta = x2 `primIntSub` x1
      y' = y `primIntSub` delta
      go x = if x `primIntGT` y' then [x] else x : go (x `primIntAdd` delta)
    in x1 : go x2

efttIntDown :: Int -> Int -> Int -> [Int]
-- x2 <= x1
efttIntDown x1 x2 y
  | y `primIntGT` x2 = if y `primIntGT` x1 then [] else [x1]
  | otherwise =
    let
      delta = x2 `primIntSub` x1
      y' = y `primIntSub` delta
      go x = if x `primIntLT` y' then [x] else x : go (x `primIntAdd` delta)
    in x1 : go x2

-- This instance is difficult to put in Data.Int,
-- so it gets to live here.
instance Enum Int where
  succ x = if x `primIntEQ` maxInt then error "Int.succ: overflow" else x `primIntAdd` 1
  pred x = if x `primIntEQ` minInt then error "Int.pred: underflow" else x `primIntSub` 1
  toEnum x = x
  fromEnum x = x
  enumFrom n = eftInt n maxInt
  enumFromThen x1 x2
    | x2 `primIntGE` x1 = efttIntUp x1 x2 maxInt
    | otherwise         = efttIntDown x1 x2 minInt
  enumFromTo = eftInt
  enumFromThenTo x1 x2 y
    | x2 `primIntGE` x1 = efttIntUp x1 x2 y
    | otherwise         = efttIntDown x1 x2 y

minInt, maxInt :: Int
minInt = primWordToInt ((primWordInv (0::Word) `primWordQuot` 2) `primWordAdd` 1)
maxInt = primWordToInt  (primWordInv (0::Word) `primWordQuot` 2)
