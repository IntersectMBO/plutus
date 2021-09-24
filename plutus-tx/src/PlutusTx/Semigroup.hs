{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}
module PlutusTx.Semigroup (Semigroup (..), Max (..), Min (..)) where

import                          Data.Monoid       (First (..))
import                          Data.Semigroup    (Dual (..), Endo (..))
import                          PlutusTx.Base
import                qualified PlutusTx.Builtins as Builtins
import                          PlutusTx.Functor
import                          PlutusTx.List     ((++))
import {-# SOURCE #-}           PlutusTx.Maybe
import {-# SOURCE #-}           PlutusTx.Ord      (Ord (..), Ordering (..))

{- HLINT ignore -}

infixr 6 <>

-- | Plutus Tx version of 'Data.Semigroup.Semigroup'.
class Semigroup a where
    -- | Plutus Tx version of '(Data.Semigroup.<>)'.
    (<>) :: a -> a -> a
    -- sconcat and stimes deliberately omitted, to make this a one-method class which has a
    -- simpler representation

instance Semigroup Builtins.BuiltinByteString where
    {-# INLINABLE (<>) #-}
    (<>) = Builtins.appendByteString

instance Semigroup Builtins.BuiltinString where
    {-# INLINABLE (<>) #-}
    (<>) = Builtins.appendString

instance Semigroup [a] where
    {-# INLINABLE (<>) #-}
    (<>) = (++)

instance (Semigroup a, Semigroup b) => Semigroup (a, b) where
    {-# INLINABLE (<>) #-}
    (a1, b1) <> (a2, b2) = (a1 <> a2, b1 <> b2)

instance Semigroup a => Semigroup (Maybe a) where
    Just a1 <> Just a2 = Just (a1 <> a2)
    Just a1 <> Nothing = Just a1
    Nothing <> Just a2 = Just a2
    Nothing <> Nothing = Nothing

instance Semigroup Ordering where
    LT <> _ = LT
    EQ <> y = y
    GT <> _ = GT

instance Semigroup () where
    _ <> _ = ()

instance Semigroup a => Semigroup (Dual a) where
    {-# INLINABLE (<>) #-}
    Dual a1 <> Dual a2 = Dual (a2 <> a1)

instance Semigroup (Endo a) where
    {-# INLINABLE (<>) #-}
    Endo f1 <> Endo f2 = Endo (f1 . f2)

instance Semigroup (First a) where
    {-# INLINABLE (<>) #-}
    First Nothing <> b = b
    a             <> _ = a

newtype Max a = Max { getMax :: a }

instance Functor Max where
    {-# INLINABLE fmap #-}
    fmap f (Max a) = Max (f a)

instance Ord a => Semigroup (Max a) where
    {-# INLINABLE (<>) #-}
    (Max a1) <> (Max a2) = Max (max a1 a2)

newtype Min a = Min { getMin :: a }

instance Functor Min where
    {-# INLINABLE fmap #-}
    fmap f (Min a) = Min (f a)

instance Ord a => Semigroup (Min a) where
    {-# INLINABLE (<>) #-}
    (Min a1) <> (Min a2) = Min (min a1 a2)
