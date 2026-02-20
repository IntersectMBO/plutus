{-# OPTIONS_GHC -fno-ignore-interface-pragmas #-}
{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}
{-# OPTIONS_GHC -fno-specialise #-}

module PlutusTx.Monoid (Monoid (..), mappend, mconcat, Group (..), gsub) where

import Data.Monoid (First (..))
import Data.Semigroup (Dual (..), Endo (..))
import PlutusTx.Base (id)
import PlutusTx.Builtins qualified as Builtins
import PlutusTx.List
import PlutusTx.Maybe
import PlutusTx.Ord
import PlutusTx.Semigroup

{- HLINT ignore -}

-- | Plutus Tx version of 'Data.Monoid.Monoid'.
class Semigroup a => Monoid a where
  -- | Plutus Tx version of 'Data.Monoid.mempty'.
  mempty :: a

-- mappend and mconcat deliberately omitted, to make this a one-method class which has a
-- simpler representation

-- | Plutus Tx version of 'Data.Monoid.mappend'.
mappend :: Monoid a => a -> a -> a
mappend = (<>)
{-# INLINEABLE mappend #-}

-- | Plutus Tx version of 'Data.Monoid.mconcat'.
mconcat :: Monoid a => [a] -> a
mconcat = foldr mappend mempty
{-# INLINEABLE mconcat #-}

instance Monoid Builtins.BuiltinByteString where
  {-# INLINEABLE mempty #-}
  mempty = Builtins.emptyByteString

instance Monoid Builtins.BuiltinString where
  {-# INLINEABLE mempty #-}
  mempty = Builtins.emptyString

instance Monoid [a] where
  {-# INLINEABLE mempty #-}
  mempty = []

instance Semigroup a => Monoid (Maybe a) where
  {-# INLINEABLE mempty #-}
  mempty = Nothing

instance Monoid () where
  {-# INLINEABLE mempty #-}
  mempty = ()

instance (Monoid a, Monoid b) => Monoid (a, b) where
  {-# INLINEABLE mempty #-}
  mempty = (mempty, mempty)

instance Monoid a => Monoid (Dual a) where
  {-# INLINEABLE mempty #-}
  mempty = Dual mempty

instance Monoid (Endo a) where
  {-# INLINEABLE mempty #-}
  mempty = Endo id

instance Monoid (First a) where
  {-# INLINEABLE mempty #-}
  mempty = First Nothing

instance Monoid Ordering where
  {-# INLINEABLE mempty #-}
  mempty = EQ

class Monoid a => Group a where
  inv :: a -> a

gsub :: Group a => a -> a -> a
gsub x y = x <> inv y
{-# INLINEABLE gsub #-}
