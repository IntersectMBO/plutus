module PlutusTx.Ord.Class
  ( Ord (..)
  , Ordering (..)
  , thenCmp
  ) where

{-
  We export off-chain Haskell's Ordering type as on-chain Plutus's
  Ordering type since they are the same.
-}

import PlutusTx.Bool (Bool (..))
import PlutusTx.Builtins qualified as Builtins
import PlutusTx.Eq.Class (Eq (..))
import Prelude (Ordering (..))

infix 4 <, <=, >, >=

-- Copied from the GHC definition

{-| The 'Ord' class is used for totally ordered datatypes.

Minimal complete definition: either 'compare' or '<='.
Using 'compare' can be more efficient for complex types. -}
class Eq a => Ord a where
  compare :: a -> a -> Ordering
  (<), (<=), (>), (>=) :: a -> a -> Bool
  max, min :: a -> a -> a

  {-# INLINEABLE compare #-}
  compare x y =
    if x == y
      then EQ
      -- NB: must be '<=' not '<' to validate the
      -- above claim about the minimal things that
      -- can be defined for an instance of Ord:
      else
        if x <= y
          then LT
          else GT

  {-# INLINEABLE (<) #-}
  x < y = case compare x y of LT -> True; _ -> False
  {-# INLINEABLE (<=) #-}
  x <= y = case compare x y of GT -> False; _ -> True
  {-# INLINEABLE (>) #-}
  x > y = case compare x y of GT -> True; _ -> False
  {-# INLINEABLE (>=) #-}
  x >= y = case compare x y of LT -> False; _ -> True

  -- These two default methods use '<=' rather than 'compare'
  -- because the latter is often more expensive
  {-# INLINEABLE max #-}
  max x y = if x <= y then y else x
  {-# INLINEABLE min #-}
  min x y = if x <= y then x else y
  {-# MINIMAL compare | (<=) #-}

instance Ord Builtins.Integer where
  {-# INLINEABLE (<) #-}
  (<) = Builtins.lessThanInteger
  {-# INLINEABLE (<=) #-}
  (<=) = Builtins.lessThanEqualsInteger
  {-# INLINEABLE (>) #-}
  (>) = Builtins.greaterThanInteger
  {-# INLINEABLE (>=) #-}
  (>=) = Builtins.greaterThanEqualsInteger

instance Ord Builtins.BuiltinByteString where
  {-# INLINEABLE (<) #-}
  (<) = Builtins.lessThanByteString
  {-# INLINEABLE (<=) #-}
  (<=) = Builtins.lessThanEqualsByteString
  {-# INLINEABLE (>) #-}
  (>) = Builtins.greaterThanByteString
  {-# INLINEABLE (>=) #-}
  (>=) = Builtins.greaterThanEqualsByteString

{-| Lexicographic combination of two orderings. Used by 'deriveOrd' TH
to avoid a direct reference to 'GHC.Base.<>' whose module path varies
across GHC versions. -}
{-# INLINEABLE thenCmp #-}
thenCmp :: Ordering -> Ordering -> Ordering
thenCmp EQ y = y
thenCmp x _ = x
