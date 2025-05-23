{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}

module PlutusTx.Enum (Enum (..)) where

import PlutusTx.Bool (Bool (..), otherwise)
import PlutusTx.Builtins
import PlutusTx.Eq ((==))
import PlutusTx.ErrorCodes
import PlutusTx.List
import PlutusTx.Ord (Ord (..), Ordering (..))
import PlutusTx.Trace

-- | Class 'Enum' defines operations on sequentially ordered types.
class Enum a where
  {-| The successor of a value.  For numeric types, 'succ' adds 1.

  For types that implement 'Ord', @succ x@ should be the least element
  that is greater than @x@, and 'error' if there is none.
  -}
  succ :: a -> a

  {-| The predecessor of a value.  For numeric types, 'pred' subtracts 1.

  For types that implement 'Ord', @pred x@ should be the greatest element
  that is less than @x@, and 'error' if there is none.
  -}
  pred :: a -> a

  -- | Convert from an 'Integer'.
  toEnum :: Integer -> a

  -- | Convert to an 'Integer'.
  fromEnum :: a -> Integer

  -- | Construct a list from the given range (corresponds to [a..b]).
  enumFromTo :: a -> a -> [a]

  {-| Construct a list from the given range (corresponds to [a,b..c]).  This
  has the same semantics as the Haskell version,so if a==b and c>=b then you
  get an infinite list, which you probably don't want in Plutus Core.
  -}
  enumFromThenTo :: a -> a -> a -> [a]

instance Enum Integer where
  {-# INLINEABLE succ #-}
  succ x = addInteger x 1

  {-# INLINEABLE pred #-}
  pred x = subtractInteger x 1

  {-# INLINEABLE toEnum #-}
  toEnum x = x

  {-# INLINEABLE fromEnum #-}
  fromEnum x = x

  {-# INLINEABLE enumFromTo #-}
  enumFromTo x lim
    | x > lim = []
    | otherwise = x : enumFromTo (succ x) lim

  {-# INLINEABLE enumFromThenTo #-}
  enumFromThenTo x y lim =
    if delta >= 0
      then up_list x
      else dn_list x
   where
    delta = subtractInteger y x
    up_list x1 =
      if x1 > lim
        then []
        else x1 : up_list (addInteger x1 delta)
    dn_list x1 =
      if x1 < lim
        then []
        else x1 : dn_list (addInteger x1 delta)

instance Enum () where
  {-# INLINEABLE succ #-}
  succ _ = traceError succVoidBadArgumentError

  {-# INLINEABLE pred #-}
  pred _ = traceError predVoidBadArgumentError

  {-# INLINEABLE toEnum #-}
  toEnum x
    | x == 0 = ()
    | otherwise = traceError toEnumVoidBadArgumentError

  {-# INLINEABLE fromEnum #-}
  fromEnum () = 0

  {-# INLINEABLE enumFromTo #-}
  enumFromTo _ _ = [()]

  {-# INLINEABLE enumFromThenTo #-}
  -- enumFromThenTo () () () is an infinite list of ()'s, so this isn't too useful.
  enumFromThenTo x y lim = map toEnum (enumFromThenTo (fromEnum x) (fromEnum y) (fromEnum lim))

instance Enum Bool where
  {-# INLINEABLE succ #-}
  succ False = True
  succ True  = traceError succBoolBadArgumentError

  {-# INLINEABLE pred #-}
  pred True  = False
  pred False = traceError predBoolBadArgumentError

  {-# INLINEABLE toEnum #-}
  toEnum n
    | n == 0 = False
    | n == 1 = True
    | otherwise = traceError toEnumBoolBadArgumentError

  {-# INLINEABLE fromEnum #-}
  fromEnum False = 0
  fromEnum True  = 1

  {-# INLINEABLE enumFromTo #-}
  enumFromTo x lim = map toEnum (enumFromTo (fromEnum x) (fromEnum lim))

  {-# INLINEABLE enumFromThenTo #-}
  enumFromThenTo x y lim = map toEnum (enumFromThenTo (fromEnum x) (fromEnum y) (fromEnum lim))

instance Enum Ordering where
  {-# INLINEABLE succ #-}
  succ LT = EQ
  succ EQ = GT
  succ GT = traceError succOrderingBadArgumentError

  {-# INLINEABLE pred #-}
  pred GT = EQ
  pred EQ = LT
  pred LT = traceError predOrderingBadArgumentError

  {-# INLINEABLE toEnum #-}
  toEnum n
    | n == 0 = LT
    | n == 1 = EQ
    | n == 2 = GT
  toEnum _ = traceError toEnumOrderingBadArgumentError

  {-# INLINEABLE fromEnum #-}
  fromEnum LT = 0
  fromEnum EQ = 1
  fromEnum GT = 2

  {-# INLINEABLE enumFromTo #-}
  enumFromTo x y = map toEnum (enumFromTo (fromEnum x) (fromEnum y))

  {-# INLINEABLE enumFromThenTo #-}
  enumFromThenTo x y lim = map toEnum (enumFromThenTo (fromEnum x) (fromEnum y) (fromEnum lim))
