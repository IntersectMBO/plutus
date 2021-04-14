{-# OPTIONS_GHC -fno-specialise #-}
{-# OPTIONS_GHC -fno-ignore-interface-pragmas #-}
{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}
module PlutusTx.Monoid (Monoid (..), mappend, mconcat, Group (..), gsub) where

import           Data.Monoid        (First (..))
import           Data.Semigroup     (Dual (..), Endo (..))
import qualified PlutusTx.Builtins  as Builtins
import           PlutusTx.Functor   (id)
import           PlutusTx.Semigroup
import           Prelude            hiding (Monoid (..), Semigroup (..), id, mconcat)

{-# ANN module ("HLint: ignore"::String) #-}

-- | Plutus Tx version of 'Data.Monoid.Monoid'.
class Semigroup a => Monoid a where
    -- | Plutus Tx version of 'Data.Monoid.mempty'.
    mempty :: a
    -- mappend and mconcat deliberately omitted, to make this a one-method class which has a
    -- simpler representation

{-# NOINLINE mappend #-}
-- | Plutus Tx version of 'Data.Monoid.mappend'.
mappend :: Monoid a => a -> a -> a
mappend = (<>)

{-# NOINLINE mconcat #-}
-- | Plutus Tx version of 'Data.Monoid.mconcat'.
mconcat :: Monoid a => [a] -> a
mconcat = foldr mappend mempty

instance Monoid Builtins.ByteString where
    {-# NOINLINE mempty #-}
    mempty = Builtins.emptyByteString

instance Monoid Builtins.String where
    {-# NOINLINE mempty #-}
    mempty = Builtins.emptyString

instance Monoid [a] where
    {-# NOINLINE mempty #-}
    mempty = []

instance Semigroup a => Monoid (Maybe a) where
    {-# NOINLINE mempty #-}
    mempty = Nothing

instance Monoid () where
    {-# NOINLINE mempty #-}
    mempty = ()

instance (Monoid a, Monoid b) => Monoid (a, b) where
    {-# NOINLINE mempty #-}
    mempty = (mempty, mempty)

instance Monoid a => Monoid (Dual a) where
    {-# NOINLINE mempty #-}
    mempty = Dual mempty

instance Monoid (Endo a) where
    {-# NOINLINE mempty #-}
    mempty = Endo id

instance Monoid (First a) where
    {-# NOINLINE mempty #-}
    mempty = First Nothing

class Monoid a => Group a where
    inv :: a -> a

{-# NOINLINE gsub #-}
gsub :: Group a => a -> a -> a
gsub x y = x <> inv y
