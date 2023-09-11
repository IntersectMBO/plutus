{-# LANGUAGE InstanceSigs #-}
{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}
module PlutusTx.Semigroup (Semigroup (..), Max (..), Min (..)) where

import Data.Coerce (coerce)
import Data.Monoid (First (..))
import Data.Semigroup (Dual (..), Endo (..))
import PlutusTx.Base
import PlutusTx.Builtins qualified as Builtins
import PlutusTx.Functor
import PlutusTx.List ((++))
import PlutusTx.Ord (Ord (..), Ordering (..))
import Prelude (Maybe (..))

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
    (<>) = coerce ((.) :: (a -> a) -> (a -> a) -> a -> a)

instance Semigroup (First a) where
    {-# INLINABLE (<>) #-}
    First Nothing <> b = b
    a             <> _ = a

newtype Max a = Max { getMax :: a }

instance Functor Max where
    {-# INLINABLE fmap #-}
    fmap = coerce

instance Ord a => Semigroup (Max a) where
    {-# INLINABLE (<>) #-}
    (<>) = coerce (max :: a -> a -> a)

newtype Min a = Min { getMin :: a }

instance Functor Min where
    {-# INLINABLE fmap #-}
    fmap = coerce

instance Ord a => Semigroup (Min a) where
    {-# INLINABLE (<>) #-}
    (<>) = coerce (min :: a -> a -> a)
