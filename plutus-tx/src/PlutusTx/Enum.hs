{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}
module PlutusTx.Enum (Enum(..)) where

import PlutusTx.Bool (Bool (..), otherwise)
import PlutusTx.Builtins
import PlutusTx.Eq ((==))
import PlutusTx.ErrorCodes
import PlutusTx.List
import PlutusTx.Ord (Ord (..), Ordering (..))
import PlutusTx.Trace

-- | Class 'Enum' defines operations on sequentially ordered types.
class Enum a where
  -- | The successor of a value.  For numeric types, 'succ' adds 1.
  --
  -- For types that implement 'Ord', @succ x@ should be the least element
  -- that is greater than @x@, and 'error' if there is none.
  succ :: a -> a
  -- | The predecessor of a value.  For numeric types, 'pred' subtracts 1.
  --
  -- For types that implement 'Ord', @pred x@ should be the greatest element
  -- that is less than @x@, and 'error' if there is none.
  pred :: a -> a
  -- | Convert from an 'Integer'.
  toEnum :: Integer -> a
  -- | Convert to an 'Integer'.
  fromEnum :: a -> Integer
  -- | Construct a list from the given range.
  enumFromTo :: a -> a -> [a]

instance Enum Integer where
  {-# INLINABLE succ #-}
  succ x = addInteger x 1

  {-# INLINABLE pred #-}
  pred x = subtractInteger x 1

  {-# INLINABLE toEnum #-}
  toEnum x = x

  {-# INLINABLE fromEnum #-}
  fromEnum x = x

  {-# INLINABLE enumFromTo #-}
  enumFromTo x y
    | x > y = []
    | otherwise = x : enumFromTo (succ x) y

instance Enum () where
  {-# INLINABLE succ #-}
  succ _ = traceError succVoidBadArgumentError

  {-# INLINABLE pred #-}
  pred _ = traceError predVoidBadArgumentError

  {-# INLINABLE toEnum #-}
  toEnum x | x == 0 = ()
           | otherwise = traceError toEnumVoidBadArgumentError

  {-# INLINABLE fromEnum #-}
  fromEnum () = 0

  {-# INLINABLE enumFromTo #-}
  enumFromTo _ _ = [()]

instance Enum Bool where
  {-# INLINABLE succ #-}
  succ False = True
  succ True  = traceError succBoolBadArgumentError

  {-# INLINABLE pred #-}
  pred True  = False
  pred False = traceError predBoolBadArgumentError

  {-# INLINABLE toEnum #-}
  toEnum n | n == 0    = False
           | n == 1    = True
           | otherwise = traceError toEnumBoolBadArgumentError

  {-# INLINABLE fromEnum #-}
  fromEnum False = 0
  fromEnum True  = 1

  {-# INLINABLE enumFromTo #-}
  enumFromTo x y = map toEnum (enumFromTo (fromEnum x) (fromEnum y))

instance Enum Ordering where
  {-# INLINABLE succ #-}
  succ LT = EQ
  succ EQ = GT
  succ GT = traceError succOrderingBadArgumentError

  {-# INLINABLE pred #-}
  pred GT = EQ
  pred EQ = LT
  pred LT = traceError predOrderingBadArgumentError

  {-# INLINABLE toEnum #-}
  toEnum n | n == 0 = LT
           | n == 1 = EQ
           | n == 2 = GT
  toEnum _ = traceError toEnumOrderingBadArgumentError

  {-# INLINABLE fromEnum #-}
  fromEnum LT = 0
  fromEnum EQ = 1
  fromEnum GT = 2

  {-# INLINABLE enumFromTo #-}
  enumFromTo x y = map toEnum (enumFromTo (fromEnum x) (fromEnum y))
