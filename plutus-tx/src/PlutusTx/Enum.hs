{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}
module PlutusTx.Enum (Enum(..)) where

import           PlutusTx.Builtins
import           PlutusTx.Trace
import           Prelude           hiding (Enum (..))

-- | Class 'Enum' defines operations on sequentially ordered types.
class Enum a where
  -- | the successor of a value.  For numeric types, 'succ' adds 1.
  succ :: a -> a
  -- | the predecessor of a value.  For numeric types, 'pred' subtracts 1.
  pred :: a -> a
  -- | Convert from an 'Integer'.
  toEnum :: Integer -> a
  -- | Convert to an 'Integer'.
  fromEnum :: a -> Integer

instance Enum Integer where
  {-# INLINABLE succ #-}
  succ x = addInteger x 1

  {-# INLINABLE pred #-}
  pred x = subtractInteger x 1

  {-# INLINABLE toEnum #-}
  toEnum x = x

  {-# INLINABLE fromEnum #-}
  fromEnum x = x

instance Enum () where
  {-# INLINABLE succ #-}
  succ _ = traceError "PlutusTx.Enum.().succ: bad argument"

  {-# INLINABLE pred #-}
  pred _ = traceError "PlutusTx.Enum.().pred: bad argument"

  {-# INLINABLE toEnum #-}
  toEnum x | x == 0 = ()
           | otherwise = traceError "PlutusTx.Enum.().toEnum: bad argument"

  {-# INLINABLE fromEnum #-}
  fromEnum () = 0

instance Enum Bool where
  {-# INLINABLE succ #-}
  succ False = True
  succ True  = traceError "PlutusTx.Enum.Bool.succ: bad argument"

  {-# INLINABLE pred #-}
  pred True  = False
  pred False = traceError "PlutusTx.Enum.Bool.pred: bad argument"

  {-# INLINABLE toEnum #-}
  toEnum n | n == 0    = False
           | n == 1    = True
           | otherwise = traceError "PlutusTx.Enum.Bool.toEnum: bad argument"

  {-# INLINABLE fromEnum #-}
  fromEnum False = 0
  fromEnum True  = 1

instance Enum Ordering where
  {-# INLINABLE succ #-}
  succ LT = EQ
  succ EQ = GT
  succ GT = traceError "PlutusTx.Enum.Ordering.succ: bad argument"

  {-# INLINABLE pred #-}
  pred GT = EQ
  pred EQ = LT
  pred LT = traceError "PlutusTx.Enum.Ordering.pred: bad argument"

  {-# INLINABLE toEnum #-}
  toEnum n | n == 0 = LT
           | n == 1 = EQ
           | n == 2 = GT
  toEnum _ = traceError "PlutusTx.Enum.Ordering.toEnum: bad argument"

  {-# INLINABLE fromEnum #-}
  fromEnum LT = 0
  fromEnum EQ = 1
  fromEnum GT = 2
