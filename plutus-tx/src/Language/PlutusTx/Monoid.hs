{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}
module Language.PlutusTx.Monoid (Monoid(..), mappend, mconcat) where

import qualified Language.PlutusTx.Builtins  as Builtins
import           Language.PlutusTx.Semigroup
import           Prelude                     hiding (Monoid (..), Semigroup (..), mconcat)

{-# ANN module ("HLint: ignore"::String) #-}

class Semigroup a => Monoid a where
    mempty :: a
    -- mappend and mconcat deliberately omitted, to make this a one-method class which has a
    -- simpler representation

mappend :: Monoid a => a -> a -> a
mappend = (<>)

-- | Fold a list using the monoid.
mconcat :: Monoid a => [a] -> a
mconcat = foldr mappend mempty

instance Monoid Builtins.ByteString where
    mempty = Builtins.emptyByteString

instance Monoid [a] where
    mempty = []

instance Semigroup a => Monoid (Maybe a) where
    mempty = Nothing
