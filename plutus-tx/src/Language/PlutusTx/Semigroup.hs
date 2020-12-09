{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}
module Language.PlutusTx.Semigroup (Semigroup (..)) where

import qualified Language.PlutusTx.Builtins as Builtins
import           Language.PlutusTx.List
import           Prelude                    hiding (Functor (..), Semigroup (..), (++))

{-# ANN module ("HLint: ignore"::String) #-}

class Semigroup a where
    (<>) :: a -> a -> a
    -- sconcat and stimes deliberately omitted, to make this a one-method class which has a
    -- simpler representation

instance Semigroup Builtins.ByteString where
    {-# INLINABLE (<>) #-}
    (<>) = Builtins.concatenate

instance Semigroup Builtins.String where
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
