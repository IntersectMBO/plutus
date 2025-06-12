module BitCount where

import Data.Bits
import Data.Int
import Data.Word

main :: IO ()
main = do
  -- popcount
  print $ popCount (0 :: Word8)
  print $ popCount (42 :: Word8)
  print $ popCount (64 :: Word8)
  print $ popCount (maxBound :: Word8)
  print $ popCount (0 :: Word16)
  print $ popCount (42 :: Word16)
  print $ popCount (64 :: Word16)
  print $ popCount (maxBound :: Word16)
  print $ popCount (0 :: Word32)
  print $ popCount (42 :: Word32)
  print $ popCount (64 :: Word32)
  print $ popCount (maxBound :: Word32)
  print $ popCount (0 :: Word)
  print $ popCount (42 :: Word)
  print $ popCount (64 :: Word)
  print $ popCount (maxBound :: Word) == _wordSize
  print $ popCount (0 :: Int8)
  print $ popCount (42 :: Int8)
  print $ popCount (64 :: Int8)
  print $ popCount (-1 :: Int8)
  print $ popCount (-42 :: Int8)
  print $ popCount (minBound :: Int8)
  print $ popCount (maxBound :: Int8)
  print $ popCount (0 :: Int16)
  print $ popCount (42 :: Int16)
  print $ popCount (64 :: Int16)
  print $ popCount (-1 :: Int16)
  print $ popCount (-42 :: Int16)
  print $ popCount (minBound :: Int16)
  print $ popCount (maxBound :: Int16)
  print $ popCount (0 :: Int32)
  print $ popCount (42 :: Int32)
  print $ popCount (64 :: Int32)
  print $ popCount (-1 :: Int32)
  print $ popCount (-42 :: Int32)
  print $ popCount (minBound :: Int32)
  print $ popCount (maxBound :: Int32)
  print $ popCount (0 :: Int)
  print $ popCount (42 :: Int)
  print $ popCount (64 :: Int)
  print $ popCount (-1 :: Int) == _wordSize
  print $ popCount (-42 :: Int) == _wordSize - 3
  print $ popCount (minBound :: Int)
  print $ popCount (maxBound :: Int) == _wordSize - 1

  putStrLn ""

  -- clz
  print $ countLeadingZeros (0 :: Word8)
  print $ countLeadingZeros (42 :: Word8)
  print $ countLeadingZeros (64 :: Word8)
  print $ countLeadingZeros (maxBound :: Word8)
  print $ countLeadingZeros (0 :: Word16)
  print $ countLeadingZeros (42 :: Word16)
  print $ countLeadingZeros (64 :: Word16)
  print $ countLeadingZeros (maxBound :: Word16)
  print $ countLeadingZeros (0 :: Word32)
  print $ countLeadingZeros (42 :: Word32)
  print $ countLeadingZeros (64 :: Word32)
  print $ countLeadingZeros (maxBound :: Word32)
  print $ countLeadingZeros (0 :: Word) == _wordSize
  print $ countLeadingZeros (42 :: Word) == _wordSize - 6
  print $ countLeadingZeros (64 :: Word) == _wordSize - 7
  print $ countLeadingZeros (maxBound :: Word)
  print $ countLeadingZeros (0 :: Int8)
  print $ countLeadingZeros (42 :: Int8)
  print $ countLeadingZeros (64 :: Int8)
  print $ countLeadingZeros (-1 :: Int8)
  print $ countLeadingZeros (-42 :: Int8)
  print $ countLeadingZeros (minBound :: Int8)
  print $ countLeadingZeros (maxBound :: Int8)
  print $ countLeadingZeros (0 :: Int16)
  print $ countLeadingZeros (42 :: Int16)
  print $ countLeadingZeros (64 :: Int16)
  print $ countLeadingZeros (-1 :: Int16)
  print $ countLeadingZeros (-42 :: Int16)
  print $ countLeadingZeros (minBound :: Int16)
  print $ countLeadingZeros (maxBound :: Int16)
  print $ countLeadingZeros (0 :: Int32)
  print $ countLeadingZeros (42 :: Int32)
  print $ countLeadingZeros (64 :: Int32)
  print $ countLeadingZeros (-1 :: Int32)
  print $ countLeadingZeros (-42 :: Int32)
  print $ countLeadingZeros (minBound :: Int32)
  print $ countLeadingZeros (maxBound :: Int32)
  print $ countLeadingZeros (0 :: Int) == _wordSize
  print $ countLeadingZeros (42 :: Int) == _wordSize - 6
  print $ countLeadingZeros (64 :: Int) == _wordSize - 7
  print $ countLeadingZeros (-1 :: Int)
  print $ countLeadingZeros (-42 :: Int)
  print $ countLeadingZeros (minBound :: Int)
  print $ countLeadingZeros (maxBound :: Int)

  putStrLn ""

  -- ctz
  print $ countTrailingZeros (0 :: Word8)
  print $ countTrailingZeros (42 :: Word8)
  print $ countTrailingZeros (64 :: Word8)
  print $ countTrailingZeros (maxBound :: Word8)
  print $ countTrailingZeros (0 :: Word16)
  print $ countTrailingZeros (42 :: Word16)
  print $ countTrailingZeros (64 :: Word16)
  print $ countTrailingZeros (maxBound :: Word16)
  print $ countTrailingZeros (0 :: Word32)
  print $ countTrailingZeros (42 :: Word32)
  print $ countTrailingZeros (64 :: Word32)
  print $ countTrailingZeros (maxBound :: Word32)
  print $ countTrailingZeros (0 :: Word) == _wordSize
  print $ countTrailingZeros (42 :: Word)
  print $ countTrailingZeros (64 :: Word)
  print $ countTrailingZeros (maxBound :: Word)
  print $ countTrailingZeros (0 :: Int8)
  print $ countTrailingZeros (42 :: Int8)
  print $ countTrailingZeros (64 :: Int8)
  print $ countTrailingZeros (-1 :: Int8)
  print $ countTrailingZeros (-42 :: Int8)
  print $ countTrailingZeros (minBound :: Int8)
  print $ countTrailingZeros (maxBound :: Int8)
  print $ countTrailingZeros (0 :: Int16)
  print $ countTrailingZeros (42 :: Int16)
  print $ countTrailingZeros (64 :: Int16)
  print $ countTrailingZeros (-1 :: Int16)
  print $ countTrailingZeros (-42 :: Int16)
  print $ countTrailingZeros (minBound :: Int16)
  print $ countTrailingZeros (maxBound :: Int16)
  print $ countTrailingZeros (0 :: Int32)
  print $ countTrailingZeros (42 :: Int32)
  print $ countTrailingZeros (64 :: Int32)
  print $ countTrailingZeros (-1 :: Int32)
  print $ countTrailingZeros (-42 :: Int32)
  print $ countTrailingZeros (minBound :: Int32)
  print $ countTrailingZeros (maxBound :: Int32)
  print $ countTrailingZeros (0 :: Int) == _wordSize
  print $ countTrailingZeros (42 :: Int)
  print $ countTrailingZeros (64 :: Int)
  print $ countTrailingZeros (-1 :: Int)
  print $ countTrailingZeros (-42 :: Int)
  print $ countTrailingZeros (minBound :: Int) == _wordSize - 1
  print $ countTrailingZeros (maxBound :: Int)
