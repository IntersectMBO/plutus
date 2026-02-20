{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}

-- editorconfig-checker-disable-file

module PlutusTx.Ord (Ord (..), Ordering (..)) where

{-
We export off-chain Haskell's Ordering type as on-chain Plutus's Ordering type since they are the same.
-}

import PlutusTx.Bool (Bool (..))
import PlutusTx.Builtins qualified as Builtins
import PlutusTx.Either (Either (..))
import PlutusTx.Eq
import Prelude (Maybe (..), Ordering (..))

{- HLINT ignore -}

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

instance Ord a => Ord [a] where
  {-# INLINEABLE compare #-}
  compare [] [] = EQ
  compare [] (_ : _) = LT
  compare (_ : _) [] = GT
  compare (x : xs) (y : ys) =
    case compare x y of
      EQ -> compare xs ys
      c -> c

instance Ord Bool where
  {-# INLINEABLE compare #-}
  compare b1 b2 = case b1 of
    False -> case b2 of
      False -> EQ
      True -> LT
    True -> case b2 of
      False -> GT
      True -> EQ

instance Ord a => Ord (Maybe a) where
  {-# INLINEABLE compare #-}
  compare (Just a1) (Just a2) = compare a1 a2
  compare Nothing (Just _) = LT
  compare (Just _) Nothing = GT
  compare Nothing Nothing = EQ

instance (Ord a, Ord b) => Ord (Either a b) where
  {-# INLINEABLE compare #-}
  compare (Left a1) (Left a2) = compare a1 a2
  compare (Left _) (Right _) = LT
  compare (Right _) (Left _) = GT
  compare (Right b1) (Right b2) = compare b1 b2

instance Ord () where
  {-# INLINEABLE compare #-}
  compare _ _ = EQ

instance (Ord a, Ord b) => Ord (a, b) where
  {-# INLINEABLE compare #-}
  compare (a, b) (a', b') =
    case compare a a' of
      EQ -> compare b b'
      c -> c
