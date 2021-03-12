{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}
module Language.PlutusTx.Applicative where

import           Control.Applicative       (Const (..))
import           Data.Functor.Identity     (Identity (..))
import           Language.PlutusTx.Functor
import           Language.PlutusTx.Monoid  (Monoid (..), mappend)
import           Prelude                   (Bool, Either (..), Maybe (..))

{-# ANN module "HLint: ignore" #-}

infixl 4 <*>, <*, *>

class Functor f => Applicative f where
    {-# MINIMAL pure, (<*>) #-}
    -- | Lift a value.
    pure :: a -> f a

    -- | Sequential application.
    (<*>) :: f (a -> b) -> f a -> f b

{-# INLINABLE liftA2 #-}
-- | Lift a binary function to actions.
liftA2 :: Applicative f => (a -> b -> c) -> f a -> f b -> f c
liftA2 f x = (<*>) (fmap f x)

{-# INLINABLE (*>) #-}
-- | Sequence actions, discarding the value of the first argument.
(*>) :: Applicative f => f a -> f b -> f b
a1 *> a2 = (id <$ a1) <*> a2

{-# INLINABLE (<*) #-}
-- | Sequence actions, discarding the value of the second argument.
(<*) :: Applicative f => f a -> f b -> f a
(<*) = liftA2 const

{-# INLINABLE unless #-}
unless :: (Applicative f) => Bool -> f () -> f ()
unless p s =  if p then pure () else s

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
    Identity f <*> Identity a = Identity (f a)

instance Monoid m => Applicative (Const m) where
    {-# INLINABLE pure #-}
    pure _ = Const mempty
    {-# INLINABLE (<*>) #-}
    Const m1 <*> Const m2 = Const (mappend m1 m2)
