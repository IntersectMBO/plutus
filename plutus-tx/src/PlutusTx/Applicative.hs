{-# LANGUAGE InstanceSigs #-}

module PlutusTx.Applicative where

import Control.Applicative (Const (..))
import Data.Coerce (coerce)
import Data.Functor.Identity (Identity (..))
import PlutusTx.Base
import PlutusTx.Bool (Bool)
import PlutusTx.Either (Either (..))
import PlutusTx.Functor
import PlutusTx.Maybe (Maybe (..))
import PlutusTx.Monoid (Monoid (..), mappend)

{- HLINT ignore -}

infixl 4 <*>, <*, *>

-- | Plutus Tx version of 'Control.Applicative.Applicative'.
class Functor f => Applicative f where
    {-# MINIMAL pure, (<*>) #-}
    -- | Plutus Tx version of 'Control.Applicative.pure'.
    pure :: a -> f a

    -- | Plutus Tx version of '(Control.Applicative.<*>)'.
    (<*>) :: f (a -> b) -> f a -> f b

{-# INLINABLE liftA2 #-}
-- | Plutus Tx version of 'Control.Applicative.liftA2'.
liftA2 :: Applicative f => (a -> b -> c) -> f a -> f b -> f c
liftA2 f x = (<*>) (fmap f x)

{-# INLINABLE (*>) #-}
-- | Plutus Tx version of '(Control.Applicative.*>)'.
(*>) :: Applicative f => f a -> f b -> f b
a1 *> a2 = (id <$ a1) <*> a2

{-# INLINABLE (<*) #-}
-- | Plutus Tx version of '(Control.Applicative.<*)'.
(<*) :: Applicative f => f a -> f b -> f a
(<*) = liftA2 const

{-# INLINABLE unless #-}
-- | Plutus Tx version of 'Control.Monad.unless'.
unless :: (Applicative f) => Bool -> f () -> f ()
unless p s = if p then pure () else s

instance Applicative Maybe where
    {-# INLINABLE pure #-}
    pure = Just
    {-# INLINABLE (<*>) #-}
    Nothing <*> _     = Nothing
    _ <*> Nothing     = Nothing
    Just f <*> Just x = Just (f x)

instance Applicative (Either a) where
    {-# INLINABLE pure #-}
    pure = Right
    {-# INLINABLE (<*>) #-}
    Left  e <*> _ = Left e
    Right f <*> r = fmap f r

instance Applicative Identity where
    {-# INLINABLE pure #-}
    pure = Identity
    {-# INLINABLE (<*>) #-}
    (<*>) :: forall a b. Identity (a -> b) -> Identity a -> Identity b
    (<*>) = coerce (id :: (a -> b) -> a -> b)

instance Monoid m => Applicative (Const m) where
    {-# INLINABLE pure #-}
    pure _ = Const mempty
    {-# INLINABLE (<*>) #-}
    (<*>) = coerce (mappend :: m -> m -> m)
