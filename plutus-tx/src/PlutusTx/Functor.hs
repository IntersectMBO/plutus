{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE LambdaCase   #-}
{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}
module PlutusTx.Functor (Functor(..), (<$>), (<$)) where

import Control.Applicative (Const (..))
import Data.Functor.Identity (Identity (..))

import Data.Coerce (coerce)
import PlutusTx.Base
import PlutusTx.Either (Either (..))
import Prelude (Maybe (..))

{- HLINT ignore -}

-- | Plutus Tx version of 'Data.Functor.Functor'.
class Functor f where
    -- | Plutus Tx version of 'Data.Functor.fmap'.
    fmap :: (a -> b) -> f a -> f b

    -- (<$) deliberately omitted, to make this a one-method class which has a
    -- simpler representation

infixl 4 <$>
-- | Plutus Tx version of '(Data.Functor.<$>)'.
{-# INLINABLE (<$>) #-}
(<$>) :: Functor f => (a -> b) -> f a -> f b
(<$>) = fmap

infixl 4 <$
{-# INLINABLE (<$) #-}
-- | Plutus Tx version of '(Data.Functor.<$)'.
(<$) :: Functor f => a -> f b -> f a
(<$) a = fmap (const a)

instance Functor [] where
    {-# INLINABLE fmap #-}
    fmap f = go where
        go = \case
            []   -> []
            x:xs -> f x : go xs

instance Functor Maybe where
    {-# INLINABLE fmap #-}
    fmap f (Just a) = Just (f a)
    fmap _ Nothing  = Nothing

instance Functor (Either c) where
    {-# INLINABLE fmap #-}
    fmap f (Right a) = Right (f a)
    fmap _ (Left c)  = Left c

instance Functor ((,) c) where
    {-# INLINABLE fmap #-}
    fmap f (c, a) = (c, f a)

instance Functor Identity where
    {-# INLINABLE fmap #-}
    fmap :: forall a b. (a -> b) -> Identity a -> Identity b
    fmap = coerce (id :: (a -> b) -> a -> b)

instance Functor (Const m) where
    {-# INLINABLE fmap #-}
    fmap _ = coerce (id :: m -> m)
