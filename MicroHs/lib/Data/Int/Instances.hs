module Data.Int.Instances() where
import qualified Prelude()
import Primitives
import Control.Error
import Data.Bits
import Data.Bool
import Data.Bounded
import Data.Coerce
import Data.Enum
import Data.Eq
import Data.Function
import Data.Int.IntN
import Data.Integer_Type
import Data.Integral
import Data.List
import Data.Maybe_Type
import Data.Num
import Data.Ord
import Data.Ratio_Type
import Data.Real
import Numeric.Show
import Text.Show

--------------------------------------------------------------------------------
----    Int8

-- Do sign extension by shifting.
i8 :: Int -> Int8
i8 w = I8 ((w `primIntShl` n) `primIntShr` n)
  where n = _wordSize `primIntSub` 8

bin8 :: (Int -> Int -> Int) -> (Int8 -> Int8 -> Int8)
bin8 op (I8 x) (I8 y) = i8 (x `op` y)

bini8 :: (Int -> Int -> Int) -> (Int8 -> Int -> Int8)
bini8 op (I8 x) y = i8 (x `op` y)

cmp8 :: (Int -> Int -> a) -> (Int8 -> Int8 -> a)
cmp8 op (I8 x) (I8 y) = x `op` y

una8 :: (Int -> Int) -> (Int8 -> Int8)
una8 op (I8 x) = i8 (op x)

instance Num Int8 where
  (+)  = bin8 primIntAdd
  (-)  = bin8 primIntSub
  (*)  = bin8 primIntMul
  abs x = x
  signum x = if x < 0 then -1 else if x > 0 then 1 else 0
  fromInteger i = i8 (_integerToInt i)

instance Integral Int8 where
  quot = bin8 primIntQuot
  rem  = bin8 primIntRem
  toInteger = _intToInteger . unI8

instance Bounded Int8 where
  minBound = i8 0x80
  maxBound = i8 0x7f

instance Real Int8 where
  toRational = _integerToRational . _intToInteger . unI8

instance Show Int8 where
  showsPrec = showIntegral

{- in Text.Read.Internal
instance Read Int8 where
  readsPrec = readIntegral
-}

instance Enum Int8 where
  succ x = if x == maxBound then error "Int8.succ: overflow" else x + 1
  pred x = if x == minBound then error "Int8.pred: underflow" else x - 1
  toEnum = i8
  fromEnum = unI8
  enumFrom n = enumFromTo n maxBound
  enumFromThen n m
    | m >= n = enumFromThenTo n m maxBound
    | otherwise = enumFromThenTo n m minBound
  enumFromTo = coerce (enumFromTo @Int)
  enumFromThenTo = coerce (enumFromThenTo @Int)

instance Eq Int8 where
  (==) = cmp8 primIntEQ
  (/=) = cmp8 primIntNE

instance Ord Int8 where
  compare = cmp8 primIntCompare
  (<)  = cmp8 primIntLT
  (<=) = cmp8 primIntLE
  (>)  = cmp8 primIntGT
  (>=) = cmp8 primIntGE

instance Bits Int8 where
  (.&.) = bin8 primIntAnd
  (.|.) = bin8 primIntOr
  xor   = bin8 primIntXor
  complement = una8 primIntInv
  x `shiftL` i
    | i < 0 = _overflowError
    | i >= 8 = 0
    | True = x `unsafeShiftL` i
  unsafeShiftL = bini8 primIntShl
  x `shiftR` i
    | i < 0 = _overflowError
    | i >= 8 = 0
    | True = x `unsafeShiftR` i
  unsafeShiftR = bini8 primIntShr
  bitSizeMaybe _ = Just 8
  bitSize _ = 8
  bit = bitDefault
  testBit = testBitDefault
  popCount (I8 x) = primIntPopcount (x .&. 0xff)
  zeroBits = 0
  isSigned _ = True

instance FiniteBits Int8 where
  finiteBitSize _ = 8
  countLeadingZeros (I8 x) = primIntClz (x .&. 0xff) - (_wordSize - 8)
  countTrailingZeros (I8 x) = if x == 0 then 8 else primIntCtz x

--------------------------------------------------------------------------------
----    Int16

-- Do sign extension by shifting.
i16 :: Int -> Int16
i16 w = I16 ((w `primIntShl` n) `primIntShr` n)
  where n = _wordSize `primIntSub` 16

bin16 :: (Int -> Int -> Int) -> (Int16 -> Int16 -> Int16)
bin16 op (I16 x) (I16 y) = i16 (x `op` y)

bini16 :: (Int -> Int -> Int) -> (Int16 -> Int -> Int16)
bini16 op (I16 x) y = i16 (x `op` y)

cmp16 :: (Int -> Int -> a) -> (Int16 -> Int16 -> a)
cmp16 op (I16 x) (I16 y) = x `op` y

una16 :: (Int -> Int) -> (Int16 -> Int16)
una16 op (I16 x) = i16 (op x)

instance Num Int16 where
  (+)  = bin16 primIntAdd
  (-)  = bin16 primIntSub
  (*)  = bin16 primIntMul
  abs x = x
  signum x = if x < 0 then -1 else if x > 0 then 1 else 0
  fromInteger i = i16 (_integerToInt i)

instance Integral Int16 where
  quot = bin16 primIntQuot
  rem  = bin16 primIntRem
  toInteger = _intToInteger . unI16

instance Bounded Int16 where
  minBound = i16 0x8000
  maxBound = i16 0x7fff

instance Real Int16 where
  toRational = _integerToRational . _intToInteger . unI16

instance Show Int16 where
  showsPrec = showIntegral

{- in Text.Read.Internal
instance Read Int16 where
  readsPrec = readIntegral
-}

instance Enum Int16 where
  succ x = if x == maxBound then error "Int16.succ: overflow" else x + 1
  pred x = if x == minBound then error "Int16.pred: underflow" else x - 1
  toEnum = i16
  fromEnum = unI16
  enumFrom n = enumFromTo n maxBound
  enumFromThen n m
    | m >= n = enumFromThenTo n m maxBound
    | otherwise = enumFromThenTo n m minBound
  enumFromTo = coerce (enumFromTo @Int)
  enumFromThenTo = coerce (enumFromThenTo @Int)

instance Eq Int16 where
  (==) = cmp16 primIntEQ
  (/=) = cmp16 primIntNE

instance Ord Int16 where
  compare = cmp16 primIntCompare
  (<)  = cmp16 primIntLT
  (<=) = cmp16 primIntLE
  (>)  = cmp16 primIntGT
  (>=) = cmp16 primIntGE

instance Bits Int16 where
  (.&.) = bin16 primIntAnd
  (.|.) = bin16 primIntOr
  xor   = bin16 primIntXor
  complement = una16 primIntInv
  x `shiftL` i
    | i < 0 = _overflowError
    | i >= 16 = 0
    | True = x `unsafeShiftL` i
  unsafeShiftL = bini16 primIntShl
  x `shiftR` i
    | i < 0 = _overflowError
    | i >= 16 = 0
    | True = x `unsafeShiftR` i
  unsafeShiftR = bini16 primIntShr
  bitSizeMaybe _ = Just 16
  bitSize _ = 16
  bit = bitDefault
  testBit = testBitDefault
  popCount (I16 x) = primIntPopcount (x .&. 0xffff)
  zeroBits = 0
  isSigned _ = True

instance FiniteBits Int16 where
  finiteBitSize _ = 16
  countLeadingZeros (I16 x) = primIntClz (x .&. 0xffff) - (_wordSize - 16)
  countTrailingZeros (I16 x) = if x == 0 then 16 else primIntCtz x

--------------------------------------------------------------------------------
----    Int32

-- Do sign extension by shifting.
i32 :: Int -> Int32
i32 w = if n == 0 then I32 w else I32 ((w `primIntShl` n) `primIntShr` n)
  where n = _wordSize `primIntSub` 32

bin32 :: (Int -> Int -> Int) -> (Int32 -> Int32 -> Int32)
bin32 op (I32 x) (I32 y) = i32 (x `op` y)

bini32 :: (Int -> Int -> Int) -> (Int32 -> Int -> Int32)
bini32 op (I32 x) y = i32 (x `op` y)

cmp32 :: (Int -> Int -> a) -> (Int32 -> Int32 -> a)
cmp32 op (I32 x) (I32 y) = x `op` y

una32 :: (Int -> Int) -> (Int32 -> Int32)
una32 op (I32 x) = i32 (op x)

instance Num Int32 where
  (+)  = bin32 primIntAdd
  (-)  = bin32 primIntSub
  (*)  = bin32 primIntMul
  abs x = x
  signum x = if x < 0 then -1 else if x > 0 then 1 else 0
  fromInteger i = i32 (_integerToInt i)

instance Integral Int32 where
  quot = bin32 primIntQuot
  rem  = bin32 primIntRem
  toInteger = _intToInteger . unI32

instance Bounded Int32 where
  minBound = i32 0x80000000
  maxBound = i32 0x7fffffff

instance Real Int32 where
  toRational = _integerToRational . _intToInteger . unI32

instance Show Int32 where
  showsPrec = showIntegral

{- in Text.Read.Internal
instance Read Int32 where
  readsPrec = readIntegral
-}

instance Enum Int32 where
  succ x = if x == maxBound then error "Int32.succ: overflow" else x + 1
  pred x = if x == minBound then error "Int32.pred: underflow" else x - 1
  toEnum = i32
  fromEnum = unI32
  enumFrom n = enumFromTo n maxBound
  enumFromThen n m
    | m >= n = enumFromThenTo n m maxBound
    | otherwise = enumFromThenTo n m minBound
  enumFromTo = coerce (enumFromTo @Int)
  enumFromThenTo = coerce (enumFromThenTo @Int)

instance Eq Int32 where
  (==) = cmp32 primIntEQ
  (/=) = cmp32 primIntNE

instance Ord Int32 where
  compare = cmp32 primIntCompare
  (<)  = cmp32 primIntLT
  (<=) = cmp32 primIntLE
  (>)  = cmp32 primIntGT
  (>=) = cmp32 primIntGE

instance Bits Int32 where
  (.&.) = bin32 primIntAnd
  (.|.) = bin32 primIntOr
  xor   = bin32 primIntXor
  complement = una32 primIntInv
  x `shiftL` i
    | i < 0 = _overflowError
    | i >= 32 = 0
    | True = x `unsafeShiftL` i
  unsafeShiftL = bini32 primIntShl
  x `shiftR` i
    | i < 0 = _overflowError
    | i >= 32 = 0
    | True = x `unsafeShiftR` i
  unsafeShiftR = bini32 primIntShr
  bitSizeMaybe _ = Just 32
  bitSize _ = 32
  bit = bitDefault
  testBit = testBitDefault
  popCount (I32 x) = primIntPopcount (x .&. 0xffffffff)
  zeroBits = 0
  isSigned _ = True

instance FiniteBits Int32 where
  finiteBitSize _ = 32
  countLeadingZeros (I32 x) = primIntClz (x .&. 0xffffffff) - (_wordSize - 32)
  countTrailingZeros (I32 x) = if x == 0 then 32 else primIntCtz x

--------------------------------------------------------------------------------
----    Int64

-- Do sign extension by shifting.
i64 :: Int -> Int64
i64 w = if _wordSize == 64 then I64 w else error "No Int64"

bin64 :: (Int -> Int -> Int) -> (Int64 -> Int64 -> Int64)
bin64 op (I64 x) (I64 y) = i64 (x `op` y)

bini64 :: (Int -> Int -> Int) -> (Int64 -> Int -> Int64)
bini64 op (I64 x) y = i64 (x `op` y)

cmp64 :: (Int -> Int -> a) -> (Int64 -> Int64 -> a)
cmp64 op (I64 x) (I64 y) = x `op` y

una64 :: (Int -> Int) -> (Int64 -> Int64)
una64 op (I64 x) = i64 (op x)

instance Num Int64 where
  (+)  = bin64 primIntAdd
  (-)  = bin64 primIntSub
  (*)  = bin64 primIntMul
  abs x = x
  signum x = if x < 0 then -1 else if x > 0 then 1 else 0
  fromInteger i = i64 (_integerToInt i)

instance Integral Int64 where
  quot = bin64 primIntQuot
  rem  = bin64 primIntRem
  toInteger = _intToInteger . unI64

instance Bounded Int64 where
  minBound = i64 0x8000000000000000
  maxBound = i64 0x7fffffffffffffff

instance Real Int64 where
  toRational = _integerToRational . _intToInteger . unI64

instance Show Int64 where
  showsPrec = showIntegral

{- in Text.Read.Internal
instance Read Int64 where
  readsPrec = readIntegral
-}

instance Enum Int64 where
  succ x = if x == maxBound then error "Int64.succ: overflow" else x + 1
  pred x = if x == minBound then error "Int64.pred: underflow" else x - 1
  toEnum = i64
  fromEnum = unI64
  enumFrom n = enumFromTo n maxBound
  enumFromThen n m
    | m >= n = enumFromThenTo n m maxBound
    | otherwise = enumFromThenTo n m minBound
  enumFromTo = coerce (enumFromTo @Int)
  enumFromThenTo = coerce (enumFromThenTo @Int)

instance Eq Int64 where
  (==) = cmp64 primIntEQ
  (/=) = cmp64 primIntNE

instance Ord Int64 where
  compare = cmp64 primIntCompare
  (<)  = cmp64 primIntLT
  (<=) = cmp64 primIntLE
  (>)  = cmp64 primIntGT
  (>=) = cmp64 primIntGE

instance Bits Int64 where
  (.&.) = bin64 primIntAnd
  (.|.) = bin64 primIntOr
  xor   = bin64 primIntXor
  complement = una64 primIntInv
  x `shiftL` i
    | i < 0 = _overflowError
    | i >= 64 = 0
    | True = x `unsafeShiftL` i
  unsafeShiftL = bini64 primIntShl
  x `shiftR` i
    | i < 0 = _overflowError
    | i >= 64 = 0
    | True = x `unsafeShiftR` i
  unsafeShiftR = bini64 primIntShr
  bitSizeMaybe _ = Just 64
  bitSize _ = 64
  bit = bitDefault
  testBit = testBitDefault
  popCount (I64 x) = primIntPopcount x
  zeroBits = 0
  isSigned _ = True

instance FiniteBits Int64 where
  finiteBitSize _ = 64
  countLeadingZeros = primIntClz . unI64
  countTrailingZeros = primIntCtz . unI64
