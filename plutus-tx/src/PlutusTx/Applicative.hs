{-# LANGUAGE InstanceSigs #-}

module PlutusTx.Applicative where

import Control.Applicative (Const (..))
import Data.Coerce (coerce)
import Data.Functor.Identity (Identity (..))
import PlutusTx.Base
import PlutusTx.Bool (Bool)
import PlutusTx.Either (Either (..))
import PlutusTx.Functor
import PlutusTx.List qualified as List
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

-- | Plutus Tx version of 'Control.Applicative.liftA2'.
liftA2 :: Applicative f => (a -> b -> c) -> f a -> f b -> f c
liftA2 f x = (<*>) (fmap f x)
{-# INLINEABLE liftA2 #-}

-- | Plutus Tx version of '(Control.Applicative.*>)'.
(*>) :: Applicative f => f a -> f b -> f b
a1 *> a2 = (id <$ a1) <*> a2
{-# INLINEABLE (*>) #-}

-- | Plutus Tx version of '(Control.Applicative.<*)'.
(<*) :: Applicative f => f a -> f b -> f a
(<*) = liftA2 const
{-# INLINEABLE (<*) #-}

-- | Plutus Tx version of 'Control.Monad.unless'.
unless :: Applicative f => Bool -> f () -> f ()
unless p s = if p then pure () else s
{-# INLINEABLE unless #-}

instance Applicative Maybe where
  {-# INLINEABLE pure #-}
  pure = Just
  {-# INLINEABLE (<*>) #-}
  Nothing <*> _ = Nothing
  _ <*> Nothing = Nothing
  Just f <*> Just x = Just (f x)

instance Applicative (Either a) where
  {-# INLINEABLE pure #-}
  pure = Right
  {-# INLINEABLE (<*>) #-}
  Left e <*> _ = Left e
  Right f <*> r = fmap f r

instance Applicative [] where
  {-# INLINEABLE pure #-}
  pure x = [x]
  {-# INLINEABLE (<*>) #-}
  fs <*> xs = List.concatMap (\f -> List.map f xs) fs

instance Applicative Identity where
  {-# INLINEABLE pure #-}
  pure = Identity
  {-# INLINEABLE (<*>) #-}
  (<*>) :: forall a b. Identity (a -> b) -> Identity a -> Identity b
  (<*>) = coerce (id :: (a -> b) -> a -> b)

instance Monoid m => Applicative (Const m) where
  {-# INLINEABLE pure #-}
  pure _ = Const mempty
  {-# INLINEABLE (<*>) #-}
  (<*>) = coerce (mappend :: m -> m -> m)
