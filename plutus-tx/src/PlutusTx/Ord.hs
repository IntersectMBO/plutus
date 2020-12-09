{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}
module PlutusTx.Ord (Ord(..), Max (..), Min (..)) where

import qualified PlutusTx.Builtins  as Builtins
import           PlutusTx.Data
import           PlutusTx.Eq
import           PlutusTx.Semigroup

import           Prelude            hiding (Eq (..), Ord (..), Semigroup (..))

{-# ANN module ("HLint: ignore"::String) #-}

infix 4 <, <=, >, >=

-- Copied from the GHC definition
-- | The 'Ord' class is used for totally ordered datatypes.
--
-- Minimal complete definition: either 'compare' or '<='.
-- Using 'compare' can be more efficient for complex types.
--
class Eq a => Ord a where
    compare              :: a -> a -> Ordering
    (<), (<=), (>), (>=) :: a -> a -> Bool
    max, min             :: a -> a -> a

    {-# NOINLINE compare #-}
    compare x y = if x == y then EQ
                  -- NB: must be '<=' not '<' to validate the
                  -- above claim about the minimal things that
                  -- can be defined for an instance of Ord:
                  else if x <= y then LT
                  else GT

    {-# NOINLINE (<) #-}
    x <  y = case compare x y of { LT -> True;  _ -> False }
    {-# NOINLINE (<=) #-}
    x <= y = case compare x y of { GT -> False; _ -> True }
    {-# NOINLINE (>) #-}
    x >  y = case compare x y of { GT -> True;  _ -> False }
    {-# NOINLINE (>=) #-}
    x >= y = case compare x y of { LT -> False; _ -> True }

    -- These two default methods use '<=' rather than 'compare'
    -- because the latter is often more expensive
    {-# NOINLINE max #-}
    max x y = if x <= y then y else x
    {-# NOINLINE min #-}
    min x y = if x <= y then x else y

instance Ord Integer where
    {-# NOINLINE (<) #-}
    (<) = Builtins.lessThanInteger
    {-# NOINLINE (<=) #-}
    (<=) = Builtins.lessThanEqInteger
    {-# NOINLINE (>) #-}
    (>) = Builtins.greaterThanInteger
    {-# NOINLINE (>=) #-}
    (>=) = Builtins.greaterThanEqInteger

instance Ord Builtins.ByteString where
    {-# NOINLINE compare #-}
    compare l r = if Builtins.lessThanByteString l r then LT else if Builtins.equalsByteString l r then EQ else GT

instance Ord a => Ord [a] where
    {-# NOINLINE compare #-}
    compare []     []     = EQ
    compare []     (_:_)  = LT
    compare (_:_)  []     = GT
    compare (x:xs) (y:ys) = compare x y <> compare xs ys

instance Ord Bool where
    {-# NOINLINE compare #-}
    compare b1 b2 = case b1 of
        False -> case b2 of
            False -> EQ
            True  -> LT
        True -> case b2 of
            False -> GT
            True  -> EQ

instance Ord a => Ord (Maybe a) where
    {-# NOINLINE compare #-}
    compare (Just a1) (Just a2) = compare a1 a2
    compare Nothing (Just _)    = LT
    compare (Just _) Nothing    = GT
    compare Nothing Nothing     = EQ

instance (Ord a, Ord b) => Ord (Either a b) where
    {-# NOINLINE compare #-}
    compare (Left a1) (Left a2)   = compare a1 a2
    compare (Left _) (Right _)    = LT
    compare (Right _) (Left _)    = GT
    compare (Right b1) (Right b2) = compare b1 b2

instance Ord () where
    {-# NOINLINE compare #-}
    compare _ _ = EQ

instance (Ord a, Ord b) => Ord (a, b) where
    {-# NOINLINE compare #-}
    compare (a, b) (a', b') = compare a a' <> compare b b'

instance Ord Data where
    {-# NOINLINE compare #-}
    compare (Constr i args) (Constr i' args') = compare i i' <> compare args args'
    compare Constr{} _                        = LT
    compare _ Constr {}                       = GT
    compare (Map entries) (Map entries')      = compare entries entries'
    compare Map{} _                           = LT
    compare _ Map{}                           = GT
    compare (List ds) (List ds')              = compare ds ds'
    compare List{} _                          = LT
    compare _ List{}                          = GT
    compare (I i) (I i')                      = compare i i'
    compare I{} _                             = LT
    compare _ I{}                             = GT
    compare (B b) (B b')                      = compare b b'

newtype Max a = Max { getMax :: a }

instance Functor Max where
    {-# NOINLINE fmap #-}
    fmap f (Max a) = Max (f a)

instance Ord a => Semigroup (Max a) where
    {-# NOINLINE (<>) #-}
    (Max a1) <> (Max a2) = Max (max a1 a2)

newtype Min a = Min { getMin :: a }

instance Functor Min where
    {-# NOINLINE fmap #-}
    fmap f (Min a) = Min (f a)

instance Ord a => Semigroup (Min a) where
    {-# NOINLINE (<>) #-}
    (Min a1) <> (Min a2) = Min (min a1 a2)
