{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}
module Language.PlutusTx.Semigroup (Semigroup (..), Max (..), Min (..)) where

import qualified Language.PlutusTx.Builtins as Builtins
import           Language.PlutusTx.Functor
import           Language.PlutusTx.List
import           Language.PlutusTx.Ord
import           Prelude                    hiding (Functor (..), Ord (..), Semigroup (..), (++))

{-# ANN module ("HLint: ignore"::String) #-}

class Semigroup a where
    (<>) :: a -> a -> a
    -- sconcat and stimes deliberately omitted, to make this a one-method class which has a
    -- simpler representation

instance Semigroup Builtins.ByteString where
    {-# INLINABLE (<>) #-}
    (<>) = Builtins.concatenate

instance Semigroup [a] where
    {-# INLINABLE (<>) #-}
    (<>) = (++)

instance Semigroup a => Semigroup (Maybe a) where
    Just a1 <> Just a2 = Just (a1 <> a2)
    Just a1 <> Nothing = Just a1
    Nothing <> Just a2 = Just a2
    Nothing <> Nothing = Nothing

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
