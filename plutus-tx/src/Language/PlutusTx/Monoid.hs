{-# OPTIONS_GHC -fno-specialise #-}
{-# OPTIONS_GHC -fno-ignore-interface-pragmas #-}
{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}
module Language.PlutusTx.Monoid (Monoid (..), mappend, mconcat, Group (..), gsub) where

import qualified Language.PlutusTx.Builtins  as Builtins
import           Language.PlutusTx.Semigroup
import           Prelude                     hiding (Monoid (..), Semigroup (..), mconcat)

{-# ANN module ("HLint: ignore"::String) #-}

class Semigroup a => Monoid a where
    mempty :: a
    -- mappend and mconcat deliberately omitted, to make this a one-method class which has a
    -- simpler representation

{-# INLINABLE mappend #-}
mappend :: Monoid a => a -> a -> a
mappend = (<>)

{-# INLINABLE mconcat #-}
-- | Fold a list using the monoid.
mconcat :: Monoid a => [a] -> a
mconcat = foldr mappend mempty

instance Monoid Builtins.ByteString where
    {-# INLINABLE mempty #-}
    mempty = Builtins.emptyByteString

instance Monoid Builtins.String where
    {-# INLINABLE mempty #-}
    mempty = Builtins.emptyString

instance Monoid [a] where
    {-# INLINABLE mempty #-}
    mempty = []

instance Semigroup a => Monoid (Maybe a) where
    {-# INLINABLE mempty #-}
    mempty = Nothing

instance Monoid () where
    {-# INLINABLE mempty #-}
    mempty = ()

instance (Monoid a, Monoid b) => Monoid (a, b) where
    {-# INLINABLE mempty #-}
    mempty = (mempty, mempty)

class Monoid a => Group a where
    inv :: a -> a

{-# INLINABLE gsub #-}
gsub :: Group a => a -> a -> a
gsub x y = x <> inv y
