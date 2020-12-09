{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}
module PlutusTx.Applicative where

import           Control.Applicative   (Const (..))
import           Data.Functor.Identity (Identity (..))
import           PlutusTx.Functor
import           PlutusTx.Monoid       (Monoid (..), mappend)
import           Prelude               (Bool, Either (..), Maybe (..))

{-# ANN module "HLint: ignore" #-}

infixl 4 <*>, <*, *>

-- | Plutus Tx version of 'Control.Applicative.Applicative'.
class Functor f => Applicative f where
    {-# MINIMAL pure, (<*>) #-}
    -- | Plutus Tx version of 'Control.Applicative.pure'.
    pure :: a -> f a

    -- | Plutus Tx version of '(Control.Applicative.<*>)'.
    (<*>) :: f (a -> b) -> f a -> f b

{-# NOINLINE liftA2 #-}
-- | Plutus Tx version of 'Control.Applicative.liftA2'.
liftA2 :: Applicative f => (a -> b -> c) -> f a -> f b -> f c
liftA2 f x = (<*>) (fmap f x)

{-# NOINLINE (*>) #-}
-- | Plutus Tx version of '(Control.Applicative.*>)'.
(*>) :: Applicative f => f a -> f b -> f b
a1 *> a2 = (id <$ a1) <*> a2

{-# NOINLINE (<*) #-}
-- | Plutus Tx version of '(Control.Applicative.<*)'.
(<*) :: Applicative f => f a -> f b -> f a
(<*) = liftA2 const

{-# NOINLINE unless #-}
-- | Plutus Tx version of 'Control.Monad.unless'.
unless :: (Applicative f) => Bool -> f () -> f ()
unless p s = if p then pure () else s

instance Applicative Maybe where
    {-# NOINLINE pure #-}
    pure = Just
    {-# NOINLINE (<*>) #-}
    Nothing <*> _     = Nothing
    _ <*> Nothing     = Nothing
    Just f <*> Just x = Just (f x)

instance Applicative (Either a) where
    {-# NOINLINE pure #-}
    pure = Right
    {-# NOINLINE (<*>) #-}
    Left  e <*> _ = Left e
    Right f <*> r = fmap f r

instance Applicative Identity where
    {-# NOINLINE pure #-}
    pure = Identity
    {-# NOINLINE (<*>) #-}
    Identity f <*> Identity a = Identity (f a)

instance Monoid m => Applicative (Const m) where
    {-# NOINLINE pure #-}
    pure _ = Const mempty
    {-# NOINLINE (<*>) #-}
    Const m1 <*> Const m2 = Const (mappend m1 m2)
