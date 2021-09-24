module PlutusTx.Ord (Ord(..), Ordering(..)) where

import qualified PlutusTx.Builtins as Builtins
import PlutusTx.Bool (Bool)
import PlutusTx.Eq (Eq)
import Prelude (Ordering(..))

infix 4 <, <=, >, >=

class Eq a => Ord a where
    compare              :: a -> a -> Ordering
    (<), (<=), (>), (>=) :: a -> a -> Bool
    max, min             :: a -> a -> a

    {-# INLINABLE compare #-}
    compare x y = if x == y then EQ
                  -- NB: must be '<=' not '<' to validate the
                  -- above claim about the minimal things that
                  -- can be defined for an instance of Ord:
                  else if x <= y then LT
                  else GT

    {-# INLINABLE (<) #-}
    x <  y = case compare x y of { LT -> True;  _ -> False }
    {-# INLINABLE (<=) #-}
    x <= y = case compare x y of { GT -> False; _ -> True }
    {-# INLINABLE (>) #-}
    x >  y = case compare x y of { GT -> True;  _ -> False }
    {-# INLINABLE (>=) #-}
    x >= y = case compare x y of { LT -> False; _ -> True }

    -- These two default methods use '<=' rather than 'compare'
    -- because the latter is often more expensive
    {-# INLINABLE max #-}
    max x y = if x <= y then y else x
    {-# INLINABLE min #-}
    min x y = if x <= y then x else y

instance Ord Builtins.Integer where
