module PlutusTx.Enum.Class (Enum (..)) where

import PlutusTx.Bool
import PlutusTx.Builtins
import PlutusTx.List
import PlutusTx.Numeric
import PlutusTx.Ord

-- | Class 'Enum' defines operations on sequentially ordered types.
class Enum a where
  {-# MINIMAL toEnum, fromEnum #-}

  {-| The successor of a value.  For numeric types, 'succ' adds 1.

  For types that implement 'Ord', @succ x@ should be the least element
  that is greater than @x@, and 'error' if there is none. -}
  succ :: a -> a

  {-| The predecessor of a value.  For numeric types, 'pred' subtracts 1.

  For types that implement 'Ord', @pred x@ should be the greatest element
  that is less than @x@, and 'error' if there is none. -}
  pred :: a -> a

  -- | Convert from an 'Integer'.
  toEnum :: Integer -> a

  -- | Convert to an 'Integer'.
  fromEnum :: a -> Integer

  -- | Construct a list from the given range (corresponds to [a..b]).
  enumFromTo :: a -> a -> [a]

  {-| Construct a list from the given range (corresponds to [a,b..c]).  This
  has the same semantics as the Haskell version,so if a==b and c>=b then you
  get an infinite list, which you probably don't want in Plutus Core. -}
  enumFromThenTo :: a -> a -> a -> [a]

  {-# INLINEABLE succ #-}
  succ x = toEnum (fromEnum x + 1)
  {-# INLINEABLE pred #-}
  pred x = toEnum (fromEnum x - 1)

  {-# INLINEABLE enumFromTo #-}
  enumFromTo x lim = map toEnum (enumFromTo (fromEnum x) (fromEnum lim))

  {-# INLINEABLE enumFromThenTo #-}
  enumFromThenTo x y lim = map toEnum (enumFromThenTo (fromEnum x) (fromEnum y) (fromEnum lim))

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
